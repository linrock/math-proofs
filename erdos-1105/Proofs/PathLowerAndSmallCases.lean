module

/-
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

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import CycleBlockAndTriangleBounds

@[expose] public section

/-!
# PathLowerAndSmallCases

Universal clique and hub path lower bounds (`PathMaxLower`), exact anti-Ramsey path formulas for `P_5`, `P_6`, and `P_7`, `K_8` three-hub rigidity, and `C_6` fourth-leaf rainbow path extractors for Erdős Problem 1105.
-/

section

open Finset

namespace ErdosProblems.PathUpperReduction

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_degrees_inside_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    (∑ v ∈ L, (H.between (↑L : Set V) (↑L : Set V)).degree v) =
      2 * (H.induce (↑L : Set V)).edgeFinset.card := by
  classical
  let A : SimpleGraph V := H.between (↑L : Set V) (↑L : Set V)
  have hsupport : A.support ⊆ (↑L : Set V) := by
    intro v hv
    obtain ⟨w, hadj⟩ := hv
    change H.Adj v w ∧ ((v ∈ L ∧ w ∈ L) ∨ (v ∈ L ∧ w ∈ L)) at hadj
    exact hadj.2.elim And.left And.left
  have hcard : (H.induce (↑L : Set V)).edgeFinset.card = A.edgeFinset.card := by
    rw [← H.card_filter_edgeFinset_toFinset_subset L]
    congr 1
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Finset.mem_filter, A, SimpleGraph.between_adj, Finset.mem_coe]
      constructor
      · rintro ⟨hxy, hsub⟩
        have hx : x ∈ L := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y))
        have hy : y ∈ L := hsub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y))
        exact ⟨hxy, Or.inl ⟨hx, hy⟩⟩
      · rintro ⟨hxy, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩ <;>
        refine ⟨hxy, ?_⟩ <;>
        intro z hz <;>
        (rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hz) with rfl | rfl <;> assumption)
  have hsum : (∑ v ∈ L, A.degree v) = ∑ v, A.degree v := by
    apply Finset.sum_subset (Finset.subset_univ L)
    intro v _ hv
    apply (A.degree_eq_zero_iff_notMem_support v).mpr
    exact fun hvs => hv (hsupport hvs)
  simpa only [hcard] using hsum.trans A.sum_degrees_eq_twice_card_edges

theorem degree_split_on_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V)
    (v : V) (hv : v ∈ L) :
    H.degree v = (H.between (↑L : Set V) (↑L : Set V)).degree v +
      (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).degree v := by
  let A : SimpleGraph V := H.between (↑L : Set V) (↑L : Set V)
  let B : SimpleGraph V := H.between (↑L : Set V) (↑(Lᶜ) : Set V)
  have hneighbors : H.neighborFinset v = A.neighborFinset v ∪ B.neighborFinset v := by
    ext w
    by_cases hw : w ∈ L <;>
      simp [A, B, SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj, hv, hw]
  have hdisjoint : Disjoint (A.neighborFinset v) (B.neighborFinset v) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwA hwB
    have hA : H.Adj v w ∧ w ∈ L := by
      simpa [A, SimpleGraph.between_adj, hv] using hwA
    have hB : H.Adj v w ∧ w ∉ L := by
      simpa [B, SimpleGraph.between_adj, hv] using hwB
    exact hB.2 hA.2
  change (H.neighborFinset v).card =
    (A.neighborFinset v).card + (B.neighborFinset v).card
  rw [hneighbors, Finset.card_union_of_disjoint hdisjoint]

theorem degree_sum_on_actual_part
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    (∑ v ∈ L, H.degree v) =
      2 * (H.induce (↑L : Set V)).edgeFinset.card +
        (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).edgeFinset.card := by
  let B : SimpleGraph V := H.between (↑L : Set V) (↑(Lᶜ) : Set V)
  have hdisjoint : Disjoint (↑L : Set V) (↑(Lᶜ) : Set V) := by
    refine Set.disjoint_left.mpr ?_
    intro v hvL hvC
    exact (Finset.mem_compl.mp hvC) hvL
  have hbip : B.IsBipartiteWith (↑L : Set V) (↑(Lᶜ) : Set V) :=
    SimpleGraph.between_isBipartiteWith hdisjoint
  have hcross : (∑ v ∈ L, B.degree v) = B.edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  calc
    (∑ v ∈ L, H.degree v) =
        ∑ v ∈ L, ((H.between (↑L : Set V) (↑L : Set V)).degree v + B.degree v) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact degree_split_on_actual_part H L v hv
    _ = (∑ v ∈ L, (H.between (↑L : Set V) (↑L : Set V)).degree v) +
        ∑ v ∈ L, B.degree v := Finset.sum_add_distrib
    _ = 2 * (H.induce (↑L : Set V)).edgeFinset.card + B.edgeFinset.card := by
      rw [sum_degrees_inside_actual_part H L, hcross]

theorem actual_cut_degree_ledger
    (H : SimpleGraph V) [DecidableRel H.Adj] (L : Finset V) :
    H.edgeFinset.card + (H.induce (↑L : Set V)).edgeFinset.card =
      (H.induce (↑(Lᶜ) : Set V)).edgeFinset.card + ∑ v ∈ L, H.degree v := by
  have hleft := degree_sum_on_actual_part H L
  have hright := degree_sum_on_actual_part H (Lᶜ)
  have hcrossEq :
      (H.between (↑(Lᶜ) : Set V) (↑(Lᶜᶜ) : Set V)).edgeFinset.card =
        (H.between (↑L : Set V) (↑(Lᶜ) : Set V)).edgeFinset.card := by
    congr 1
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.coe_compl, compl_compl]
    rw [SimpleGraph.between_comm]
  rw [hcrossEq] at hright
  have hpartition := Finset.sum_add_sum_compl L (fun v => H.degree v)
  have hhandshake := H.sum_degrees_eq_twice_card_edges
  omega

end ErdosProblems.PathUpperReduction

end

namespace Erdos1105.PathUpperDegree

theorem eight_degree_dichotomy
    (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hmin : ∀ v : Fin 8, 2 ≤ G.degree v)
    (hclosure : ∀ x y : Fin 8, x ≠ y → ¬G.Adj x y →
      G.degree x + G.degree y ≤ 6)
    (hlow : (Finset.univ.filter (fun v : Fin 8 => G.degree v = 2)).card ≤ 2) :
    ∀ v : Fin 8, G.degree v = 2 ∨ G.degree v = 3 ∨ G.degree v = 7 := by
  classical
  intro v
  by_cases hlarge : 5 ≤ G.degree v
  · have huniv : G.IsUniversal v := by
      intro w hne
      by_contra hnon
      have hsum := hclosure v w hne hnon
      have hminw := hmin w
      omega
    have hseven : G.degree v = 7 := by
      have h := (G.degree_eq_card_sub_one v).mpr huniv
      simpa using h
    exact Or.inr (Or.inr hseven)
  · have hnotfour : G.degree v ≠ 4 := by
      intro hfour
      have hcomp : Gᶜ.degree v = 3 := by
        rw [G.degree_compl]
        norm_num [hfour]
      have hcompCard : (Gᶜ.neighborFinset v).card = 3 := by
        calc
          (Gᶜ.neighborFinset v).card = Gᶜ.degree v :=
            Gᶜ.card_neighborFinset_eq_degree v
          _ = 3 := hcomp
      have hsubset : Gᶜ.neighborFinset v ⊆
          Finset.univ.filter (fun y : Fin 8 => G.degree y = 2) := by
        intro y hy
        have hyAdj : Gᶜ.Adj v y := (Gᶜ.mem_neighborFinset v y).mp hy
        obtain ⟨hne, hnon⟩ := (G.compl_adj v y).mp hyAdj
        have hsum := hclosure v y hne hnon
        have hminy := hmin y
        have htwo : G.degree y = 2 := by omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
      have hthree : 3 ≤
          (Finset.univ.filter (fun y : Fin 8 => G.degree y = 2)).card := by
        have h := Finset.card_le_card hsubset
        simpa only [hcompCard] using h
      omega
    have hminv := hmin v
    omega

end Erdos1105.PathUpperDegree

section

open Finset SimpleGraph
open scoped BigOperators

namespace ErdosProblems.PathUpperReduction.ActualK8Rigidity1105

theorem four_slot_degree_budget
    {V : Type*} [DecidableEq V] (L : Finset V) (f : V → ℕ)
    (hcard : L.card = 4) (hdegree : ∀ v ∈ L, f v ≤ 3)
    (hsum : 11 ≤ ∑ v ∈ L, f v) :
    (∀ v ∈ L, 2 ≤ f v) ∧
      (L.filter (fun v => f v = 2)).card ≤ 1 ∧
      (∑ v ∈ L, f v) + (L.filter (fun v => f v = 2)).card ≤ 12 := by
  classical
  have hmin : ∀ v ∈ L, 2 ≤ f v := by
    intro v hv
    have herase : (L.erase v).card = 3 := by
      rw [Finset.card_erase_of_mem hv, hcard]
    have hrest : (∑ w ∈ L.erase v, f w) ≤ 9 := by
      calc
        (∑ w ∈ L.erase v, f w) ≤ ∑ _w ∈ L.erase v, 3 :=
          Finset.sum_le_sum (fun w hw => hdegree w (Finset.mem_of_mem_erase hw))
        _ = 9 := by simp [herase]
    have hsplit := Finset.sum_erase_add L f hv
    omega
  let D := L.filter (fun v => f v = 2)
  let E := L.filter (fun v => ¬ f v = 2)
  have hDsum : (∑ v ∈ D, f v) = 2 * D.card := by
    calc
      (∑ v ∈ D, f v) = ∑ _v ∈ D, 2 :=
        Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = 2 * D.card := by simp [Nat.mul_comm]
  have hEsum : (∑ v ∈ E, f v) ≤ 3 * E.card := by
    calc
      (∑ v ∈ E, f v) ≤ ∑ _v ∈ E, 3 :=
        Finset.sum_le_sum (fun v hv => hdegree v (Finset.mem_filter.mp hv).1)
      _ = 3 * E.card := by simp [Nat.mul_comm]
  have hpartition : D.card + E.card = 4 := by
    simpa [D, E, hcard] using
      (Finset.card_filter_add_card_filter_not (s := L) (fun v => f v = 2))
  have hsplit : (∑ v ∈ D, f v) + (∑ v ∈ E, f v) = ∑ v ∈ L, f v := by
    exact Finset.sum_filter_add_sum_filter_not L (fun v => f v = 2) f
  have hdeficit : (∑ v ∈ L, f v) + D.card ≤ 12 := by omega
  refine ⟨hmin, ?_, hdeficit⟩
  change D.card ≤ 1
  omega

theorem four_core_edge_partition
    {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : Fintype.card V = 4) :
    J.edgeFinset.card + (Jᶜ).edgeFinset.card = 6 := by
  classical
  have hdisjoint : Disjoint J.edgeFinset (Jᶜ).edgeFinset :=
    SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  calc
    J.edgeFinset.card + (Jᶜ).edgeFinset.card =
        (J.edgeFinset ∪ (Jᶜ).edgeFinset).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ = (J ⊔ Jᶜ).edgeFinset.card := by rw [SimpleGraph.edgeFinset_sup]
    _ = (⊤ : SimpleGraph V).edgeFinset.card := by
      congr 1; ext e; simp only [SimpleGraph.mem_edgeFinset]; rw [sup_compl_eq_top]
    _ = 6 := by rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcard]; rfl

theorem four_core_low_degree_count
    {V : Type*} [Fintype V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (hcard : Fintype.card V = 4) (hedges : 5 ≤ J.edgeFinset.card) :
    (Finset.univ.filter (fun v : V => J.degree v ≤ 2)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun v : V => J.degree v ≤ 2)
  let B := Finset.univ.filter (fun v : V => ¬ J.degree v ≤ 2)
  have hmax : ∀ v : V, J.degree v ≤ 3 := by
    intro v
    have h := J.degree_lt_card_verts v
    rw [hcard] at h
    omega
  have hAsum : (∑ v ∈ A, J.degree v) ≤ 2 * A.card := by
    calc
      (∑ v ∈ A, J.degree v) ≤ ∑ _v ∈ A, 2 :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = 2 * A.card := by simp [Nat.mul_comm]
  have hBsum : (∑ v ∈ B, J.degree v) ≤ 3 * B.card := by
    calc
      (∑ v ∈ B, J.degree v) ≤ ∑ _v ∈ B, 3 :=
        Finset.sum_le_sum (fun v _ => hmax v)
      _ = 3 * B.card := by simp [Nat.mul_comm]
  have hpartition : A.card + B.card = 4 := by
    simpa [A, B, hcard] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun v : V => J.degree v ≤ 2))
  have hsplit : (∑ v ∈ A, J.degree v) + (∑ v ∈ B, J.degree v) =
      ∑ v : V, J.degree v :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V => J.degree v ≤ 2)
      (fun v => J.degree v)
  have hhand := J.sum_degrees_eq_twice_card_edges
  change A.card ≤ 2
  omega

theorem actual_induced_degree_le
    (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj] (C : Finset (Fin 8))
    (v : C) : (H.induce (↑C : Set (Fin 8))).degree v ≤ H.degree v := by
  classical
  have hsub : ((H.induce (↑C : Set (Fin 8))).neighborFinset v).map
      (Function.Embedding.subtype _) ⊆ H.neighborFinset v.val := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    exact (H.mem_neighborFinset v.val u.val).mpr
      (((H.induce (↑C : Set (Fin 8))).mem_neighborFinset v u).mp hu)
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] using hcard

/-- Four ACTUAL low-degree slots at seventeen edges force the SAME graph to
be K3 joined to five independent vertices. All equalities and hubs are derived. -/
theorem actual_three_hub_rigidity
    (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (L : Finset (Fin 8)) (hLcard : L.card = 4)
    (hdegree : ∀ v ∈ L, H.degree v ≤ 3)
    (hclosure : ∀ u v : Fin 8, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ 6)
    (hedges : 17 ≤ H.edgeFinset.card) :
    ∃ U : Finset (Fin 8), U.card = 3 ∧ H.edgeFinset.card = 18 ∧
      (∀ u ∈ U, H.IsUniversal u) ∧
      (∀ v : Fin 8, v ∉ U → H.degree v = 3) ∧
      ∀ x y : Fin 8, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U) := by
  classical
  let C := Lᶜ
  let J : SimpleGraph C := H.induce (↑C : Set (Fin 8))
  have hCcard : C.card = 4 := by simp [C, Finset.card_compl, hLcard]
  have hCvertices : Fintype.card C = 4 := by simp [hCcard]
  have hJmax : J.edgeFinset.card ≤ 6 := by
    have h := J.card_edgeFinset_le_card_choose_two
    rw [hCvertices] at h
    exact h
  have hsummax : (∑ v ∈ L, H.degree v) ≤ 12 := by
    calc
      (∑ v ∈ L, H.degree v) ≤ ∑ _v ∈ L, 3 := Finset.sum_le_sum hdegree
      _ = 12 := by simp [hLcard]
  have hledger : H.edgeFinset.card + (H.induce (↑L : Set (Fin 8))).edgeFinset.card =
      J.edgeFinset.card + ∑ v ∈ L, H.degree v :=
    ErdosProblems.PathUpperReduction.actual_cut_degree_ledger H L
  have hJfive : 5 ≤ J.edgeFinset.card := by omega
  have hsummin : 11 ≤ ∑ v ∈ L, H.degree v := by omega
  obtain ⟨hLmin, hLtwo, hdeficit⟩ :=
    four_slot_degree_budget L (fun v => H.degree v) hLcard hdegree hsummin
  have hJpartition := four_core_edge_partition J hCvertices
  have hmissing : (Jᶜ).edgeFinset.card ≤ 1 := by omega
  have hJdegree : ∀ v : C, 2 ≤ J.degree v := by
    intro v
    have hmissingDegree := (Jᶜ).degree_le_card_edgeFinset v
    have hcomplement := J.degree_compl v
    have hmax := J.degree_lt_card_verts v
    rw [hCvertices] at hcomplement hmax
    omega
  have hmin : ∀ v : Fin 8, 2 ≤ H.degree v := by
    intro v
    by_cases hv : v ∈ L
    · exact hLmin v hv
    · have hvC : v ∈ C := Finset.mem_compl.mpr hv
      have hlo := hJdegree ⟨v, hvC⟩
      have hle := actual_induced_degree_le H C ⟨v, hvC⟩
      exact hlo.trans hle
  let D := L.filter (fun v => H.degree v = 2)
  let B := C.filter (fun v => H.degree v = 2)
  let A := Finset.univ.filter (fun v : C => J.degree v ≤ 2)
  change (∑ v ∈ L, H.degree v) + D.card ≤ 12 at hdeficit
  have hAcard : A.card ≤ 2 := four_core_low_degree_count J hCvertices hJfive
  have hBsub : B ⊆ A.image (fun v : C => (v : Fin 8)) := by
    intro v hv
    obtain ⟨hvC, hvdegree⟩ := Finset.mem_filter.mp hv
    let w : C := ⟨v, hvC⟩
    have hle : J.degree w ≤ 2 := by
      have h := actual_induced_degree_le H C w
      change J.degree w ≤ H.degree v at h
      omega
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩, rfl⟩
  have hBcard : B.card ≤ 2 := by
    have h := Finset.card_le_card hBsub
    have himage : (A.image (fun v : C => (v : Fin 8))).card = A.card :=
      Finset.card_image_of_injective A Subtype.val_injective
    omega
  have hDcard : D.card ≤ 1 := hLtwo
  have hlow : (Finset.univ.filter (fun v : Fin 8 => H.degree v = 2)).card ≤ 2 := by
    have hpartition : Finset.univ.filter (fun v : Fin 8 => H.degree v = 2) = D ∪ B := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, D, B,
        C, Finset.mem_compl]
      tauto
    have hdisjoint : Disjoint D B := by
      apply Finset.disjoint_left.mpr
      intro v hvD hvB
      exact (Finset.mem_compl.mp (Finset.mem_filter.mp hvB).1)
        (Finset.mem_filter.mp hvD).1
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
    by_cases hD : D.Nonempty
    · have hDpos : 1 ≤ D.card := Finset.card_pos.mpr hD
      have hJsix : J.edgeFinset.card = 6 := by omega
      have hmissingZero : (Jᶜ).edgeFinset.card = 0 := by omega
      have hBempty : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvC, hvdegree⟩ := Finset.mem_filter.mp hv
        let w : C := ⟨v, hvC⟩
        have hmissingDegree := (Jᶜ).degree_le_card_edgeFinset w
        have hcomplement := J.degree_compl w
        have hmax := J.degree_lt_card_verts w
        have hle := actual_induced_degree_le H C w
        change J.degree w ≤ H.degree v at hle
        rw [hCvertices] at hcomplement hmax
        omega
      simp only [hBempty, Finset.card_empty, Nat.add_zero]
      omega
    · have hDzero : D.card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hD)
      omega
  have hdich := Erdos1105.PathUpperDegree.eight_degree_dichotomy H hmin hclosure hlow
  let U := Finset.univ.filter (fun v : Fin 8 => H.degree v = 7)
  let O := Uᶜ
  have hUmem : ∀ v : Fin 8, v ∈ U ↔ H.degree v = 7 := by
    intro v
    simp [U]
  have hUuniversal : ∀ v ∈ U, H.IsUniversal v := by
    intro v hv
    apply (H.degree_eq_card_sub_one v).mp
    simpa using (hUmem v).mp hv
  have hOdegree : ∀ v : Fin 8, v ∉ U → H.degree v ≤ 3 := by
    intro v hv
    have hnot : H.degree v ≠ 7 := fun h => hv ((hUmem v).mpr h)
    rcases hdich v with htwo | hthree | hseven <;> omega
  have hUneighbors : ∀ v : Fin 8, v ∉ U → U ⊆ H.neighborFinset v := by
    intro v hv u hu
    have hne : u ≠ v := by
      intro h
      exact hv (h ▸ hu)
    exact (H.mem_neighborFinset v u).mpr ((hUuniversal u hu hne).symm)
  have hUledegree : ∀ v : Fin 8, v ∉ U → U.card ≤ H.degree v := by
    intro v hv
    exact Finset.card_le_card (hUneighbors v hv)
  have hUthreeUpper : U.card ≤ 3 := by
    have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hLnonempty
    have hvnot : v ∉ U := by
      intro hvU
      have hseven := (hUmem v).mp hvU
      have hle := hdegree v hv
      omega
    have hle := hUledegree v hvnot
    have hbound := hdegree v hv
    omega
  have hUOcard : U.card + O.card = 8 := by
    simp [O]
  have hsumU : (∑ v ∈ U, H.degree v) = 7 * U.card := by
    calc
      (∑ v ∈ U, H.degree v) = ∑ _v ∈ U, 7 :=
        Finset.sum_congr rfl (fun v hv => (hUmem v).mp hv)
      _ = 7 * U.card := by simp [Nat.mul_comm]
  have hsumO : (∑ v ∈ O, H.degree v) ≤ 3 * O.card := by
    calc
      (∑ v ∈ O, H.degree v) ≤ ∑ _v ∈ O, 3 :=
        Finset.sum_le_sum (fun v hv => hOdegree v (Finset.mem_compl.mp hv))
      _ = 3 * O.card := by simp [Nat.mul_comm]
  have hsplit : (∑ v ∈ U, H.degree v) + (∑ v ∈ O, H.degree v) =
      ∑ v : Fin 8, H.degree v :=
    Finset.sum_add_sum_compl U (fun v => H.degree v)
  have hhand := H.sum_degrees_eq_twice_card_edges
  have hUcard : U.card = 3 := by omega
  have hOthree : ∀ v : Fin 8, v ∉ U → H.degree v = 3 := by
    intro v hv
    have hlo := hUledegree v hv
    have hhi := hOdegree v hv
    omega
  have hsumOexact : (∑ v ∈ O, H.degree v) = 3 * O.card := by
    calc
      (∑ v ∈ O, H.degree v) = ∑ _v ∈ O, 3 :=
        Finset.sum_congr rfl (fun v hv => hOthree v (Finset.mem_compl.mp hv))
      _ = 3 * O.card := by simp [Nat.mul_comm]
  have hHedges : H.edgeFinset.card = 18 := by omega
  refine ⟨U, hUcard, hHedges, hUuniversal, hOthree, ?_⟩
  intro x y
  constructor
  · intro hxy
    refine ⟨hxy.ne, ?_⟩
    by_contra hneither
    have hx : x ∉ U := by tauto
    have hy : y ∉ U := by tauto
    have hsub : insert y U ⊆ H.neighborFinset x := by
      intro z hz
      rcases Finset.mem_insert.mp hz with heq | hzU
      · subst z
        exact (H.mem_neighborFinset x y).mpr hxy
      · exact hUneighbors x hx hzU
    have hcard : (insert y U).card = 4 := by
      rw [Finset.card_insert_of_notMem hy, hUcard]
    have hle := Finset.card_le_card hsub
    have hdegreeX := hOthree x hx
    change (insert y U).card ≤ H.degree x at hle
    omega
  · rintro ⟨hxy, hx | hy⟩
    · exact hUuniversal x hx hxy
    · exact (hUuniversal y hy hxy.symm).symm

end ErdosProblems.PathUpperReduction.ActualK8Rigidity1105

end

namespace ErdosProblems.AntiRamseyPathFiveDiamond

open SimpleGraph

/-- Choose the two endpoints of a possible missing edge as positions `0,1`.
The remaining two vertices become positions `2,3`. -/
def orientMissing (e : Sym2 (Fin 4)) : Fin 4 → Fin 4 :=
  if e = s(0, 2) then ![0, 2, 1, 3]
  else if e = s(0, 3) then ![0, 3, 1, 2]
  else if e = s(1, 2) then ![1, 2, 0, 3]
  else if e = s(1, 3) then ![1, 3, 0, 2]
  else if e = s(2, 3) then ![2, 3, 0, 1]
  else id

theorem orientMissing_properties (e : Sym2 (Fin 4))
    (he : e ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset) :
    Function.Injective (orientMissing e) ∧
      s(orientMissing e 0, orientMissing e 1) = e := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hne : a ≠ b := by
      have hadj : (⊤ : SimpleGraph (Fin 4)).Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      exact (top_adj _ _).mp hadj
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hne rfl).elim
      | decide

/-- A graph on four vertices with at least five edges is missing at most one
complete-graph edge. -/
theorem missing_edge_card_le_one (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card) :
    ((⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset).card ≤ 1 := by
  classical
  have hsubset : G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin 4)).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  have hsix : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
  rw [Finset.card_sdiff_of_subset hsubset]
  omega

/-- If one complete-graph edge is absent, every distinct complete-graph edge
must be present under the five-edge hypothesis. -/
theorem other_edge_present (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card)
    (e₀ e₁ : Sym2 (Fin 4))
    (hmiss : e₀ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset)
    (htop : e₁ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset)
    (hne : e₁ ≠ e₀) : e₁ ∈ G.edgeFinset := by
  classical
  by_contra hnot
  have hmiss₁ : e₁ ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset :=
    Finset.mem_sdiff.mpr ⟨htop, hnot⟩
  have hpair : ({e₀, e₁} : Finset (Sym2 (Fin 4))) ⊆
      (⊤ : SimpleGraph (Fin 4)).edgeFinset \ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hmiss
    · exact hmiss₁
  have hcardpair : ({e₀, e₁} : Finset (Sym2 (Fin 4))).card = 2 := by
    have hnot : e₀ ∉ ({e₁} : Finset (Sym2 (Fin 4))) := by
      simpa only [Finset.mem_singleton] using (Ne.symm hne)
    rw [Finset.card_insert_of_notMem hnot]
    simp
  have hcard := Finset.card_le_card hpair
  have hmax := missing_edge_card_le_one G hfive
  omega

/-- The five named edges `02,03,12,13,23` are present after orienting the
possible unique missing edge to `01`. -/
theorem dense_four_has_diamond (G : SimpleGraph (Fin 4))
    [DecidableRel G.Adj] (hfive : 5 ≤ G.edgeFinset.card) :
    ∃ u : Fin 4 → Fin 4, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  let T : Finset (Sym2 (Fin 4)) := (⊤ : SimpleGraph (Fin 4)).edgeFinset
  by_cases hfull : T ⊆ G.edgeFinset
  · have hfull_adj (i j : Fin 4) (hij : i ≠ j) : G.Adj i j := by
      have htop : s(i, j) ∈ T := by
        simpa only [T, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          ((top_adj i j).mpr hij)
      have hpresent : s(i, j) ∈ G.edgeFinset := hfull htop
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hpresent
    exact ⟨id, fun _ _ h => h,
      hfull_adj 0 2 (by decide), hfull_adj 0 3 (by decide),
      hfull_adj 1 2 (by decide), hfull_adj 1 3 (by decide),
      hfull_adj 2 3 (by decide)⟩
  · obtain ⟨e, heT, heNot⟩ := Finset.not_subset.mp hfull
    have hmiss : e ∈ T \ G.edgeFinset := Finset.mem_sdiff.mpr ⟨heT, heNot⟩
    let u : Fin 4 → Fin 4 := orientMissing e
    obtain ⟨hu, hmissing⟩ := orientMissing_properties e heT
    have hadj (i j : Fin 4) (hij : i ≠ j)
        (hnot : s(i, j) ≠ s((0 : Fin 4), (1 : Fin 4))) :
        G.Adj (u i) (u j) := by
      have htop : s(u i, u j) ∈ T := by
        simpa only [T, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          ((top_adj (u i) (u j)).mpr (hu.ne hij))
      have hne : s(u i, u j) ≠ e := by
        intro heq
        have hmap : Sym2.map u s(i, j) =
            Sym2.map u s((0 : Fin 4), (1 : Fin 4)) := by
          simp only [Sym2.map_mk]
          rw [hmissing]
          exact heq
        exact hnot ((Sym2.map.injective hu) hmap)
      have hpresent := other_edge_present G hfive e s(u i, u j) hmiss htop hne
      simpa only [G.mem_edgeFinset, G.mem_edgeSet] using hpresent
    exact ⟨u, hu,
      hadj 0 2 (by decide) (by decide),
      hadj 0 3 (by decide) (by decide),
      hadj 1 2 (by decide) (by decide),
      hadj 1 3 (by decide) (by decide),
      hadj 2 3 (by decide) (by decide)⟩

end ErdosProblems.AntiRamseyPathFiveDiamond

namespace ErdosProblems.AntiRamseyPathFiveDiamond

open SimpleGraph

/-- Any four-vertex finite graph with at least five edges has an injective
five-edge diamond, regardless of its carrier type. -/
theorem dense_four_has_diamond_finite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : Fintype.card V = 4) (hfive : 5 ≤ G.edgeFinset.card) :
    ∃ u : Fin 4 → V, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  let H : SimpleGraph (Fin 4) := G.overFin hfour
  let e : G ≃g H := G.overFinIso hfour
  have hH : 5 ≤ H.edgeFinset.card := by
    have hcard : G.edgeFinset.card = H.edgeFinset.card := e.card_edgeFinset_eq
    omega
  obtain ⟨w, hw, h02, h03, h12, h13, h23⟩ := dense_four_has_diamond H hH
  let u : Fin 4 → V := fun i => e.symm (w i)
  have hu : Function.Injective u := e.symm.injective.comp hw
  refine ⟨u, hu, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact e.symm.map_adj_iff.mpr h02
    | exact e.symm.map_adj_iff.mpr h03
    | exact e.symm.map_adj_iff.mpr h12
    | exact e.symm.map_adj_iff.mpr h13
    | exact e.symm.map_adj_iff.mpr h23

/-- The five diamond adjacencies of a dense four-vertex component also hold
in its parent graph. -/
theorem dense_component_has_diamond {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : G.ConnectedComponent)
    (hfour : Fintype.card C.supp = 4)
    (hfive : 5 ≤ Nat.card C.toSimpleGraph.edgeSet) :
    ∃ u : Fin 4 → Fin n, Function.Injective u ∧
      G.Adj (u 0) (u 2) ∧ G.Adj (u 0) (u 3) ∧
      G.Adj (u 1) (u 2) ∧ G.Adj (u 1) (u 3) ∧
      G.Adj (u 2) (u 3) := by
  classical
  have hcardSupp : Fintype.card C = Fintype.card C.supp :=
    Fintype.card_congr (Equiv.refl _)
  have hfourC : Fintype.card C = 4 := hcardSupp.trans hfour
  have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.toSimpleGraph.card_edgeSet
  have hfive' : 5 ≤ C.toSimpleGraph.edgeFinset.card := by omega
  obtain ⟨w, hw, h02, h03, h12, h13, h23⟩ :=
    dense_four_has_diamond_finite C.toSimpleGraph hfourC hfive'
  let u : Fin 4 → Fin n := fun i => (w i).val
  have hu : Function.Injective u := Subtype.val_injective.comp hw
  refine ⟨u, hu, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | exact C.toSimpleGraph_hom.map_adj h02
    | exact C.toSimpleGraph_hom.map_adj h03
    | exact C.toSimpleGraph_hom.map_adj h12
    | exact C.toSimpleGraph_hom.map_adj h13
    | exact C.toSimpleGraph_hom.map_adj h23

end ErdosProblems.AntiRamseyPathFiveDiamond

namespace ErdosProblems.AntiRamseyPathFiveUpper

/-- Four Hamiltonian paths in a diamond, rooted at a degree-two vertex.
Values at indices 1, 2, 3 index their three edges among the five
diamond edges ac, ad, bc, bd, cd (numbered 0, 1, 2, 3, 4). -/
def diamondPathEdgeIndex (r : Fin 4) (i : Fin 4) : Fin 5 :=
  if r = 0 then
    if i = 1 then 0 else if i = 2 then 2 else 3
  else if r = 1 then
    if i = 1 then 1 else if i = 2 then 3 else 2
  else if r = 2 then
    if i = 1 then 0 else if i = 2 then 4 else 3
  else
    if i = 1 then 1 else if i = 2 then 4 else 2

/-- Color of the four consecutive edges of a five-vertex path formed by
attaching a new vertex to a rooted Hamiltonian path in the diamond. -/
def extendedPathColors {C : Type*} (d : Fin 5 → C) (x : C)
    (r : Fin 4) (i : Fin 4) : C :=
  if i = 0 then x else d (diamondPathEdgeIndex r i)

/-- The rooted diamond has a Hamiltonian path avoiding any one extra edge
color, provided its five edge colors are distinct. -/
theorem diamond_color_choice {C : Type*} (d : Fin 5 → C) (hd : Function.Injective d)
    (x : C) :
    ∃ r : Fin 4, Function.Injective (extendedPathColors d x r) := by
  by_cases h₀ : x = d 0
  · refine ⟨1, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₁ : x = d 1
  · refine ⟨0, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₂ : x = d 2
  · refine ⟨2, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  by_cases h₃ : x = d 3
  · refine ⟨3, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]
  refine ⟨0, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [extendedPathColors, diamondPathEdgeIndex, hd.eq_iff]

end ErdosProblems.AntiRamseyPathFiveUpper

namespace ErdosProblems.AntiRamseyPathFiveUpper

open SimpleGraph

/-- The five diamond edges ac, ad, bc, bd, cd, where an injective map
u names v, a, b, c, d at indices 0, 1, 2, 3, 4. -/
def diamondEdgeColors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 5 → Fin n)
    (hu : Function.Injective u) : Fin 5 → C :=
  fun i =>
    if i = 0 then χ.get (u 1) (u 3) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 1 then χ.get (u 1) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 2 then χ.get (u 2) (u 3) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 3 then χ.get (u 2) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else χ.get (u 3) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))

/-- Vertex orders v-a-c-b-d, v-a-d-b-c, v-a-c-d-b, v-a-d-c-b. -/
def diamondPathVertexIndex (r : Fin 4) (i : Fin 5) : Fin 5 :=
  if r = 0 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 2 else 4
  else if r = 1 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 2 else 3
  else if r = 2 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else if i = 3 then 4 else 2
  else
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 3 else 2

theorem diamondPathVertexIndex_injective (r : Fin 4) :
    Function.Injective (diamondPathVertexIndex r) := by
  fin_cases r <;> decide

theorem path_five_adj_succ (i : Fin 4) :
    (pathGraph 5).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

def pathFiveEdge (i : Fin 4) : (pathGraph 5).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), path_five_adj_succ i⟩

theorem pathFiveEdge_surjective : Function.Surjective pathFiveEdge := by
  intro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    change (pathGraph 5).Adj a b at he
    fin_cases a <;> fin_cases b <;>
      first
      | exact ⟨0, Subtype.ext (by rfl)⟩
      | exact ⟨0, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨1, Subtype.ext (by rfl)⟩
      | exact ⟨1, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨2, Subtype.ext (by rfl)⟩
      | exact ⟨2, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨3, Subtype.ext (by rfl)⟩
      | exact ⟨3, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact False.elim (by simp [pathGraph_adj] at he)

/-- Five distinct vertices whose five diamond edges have five distinct
colors force a rainbow five-vertex path, regardless of the remaining
edge colors. The missing diamond edge a-b is never used. -/
theorem rainbow_path_five_of_rainbow_diamond {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 5 → Fin n)
    (hu : Function.Injective u)
    (hd : Function.Injective (diamondEdgeColors χ u hu)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  let x := χ.get (u 0) (u 1) ((top_adj _ _).mpr (hu.ne (by decide)))
  obtain ⟨r, hr⟩ := diamond_color_choice (diamondEdgeColors χ u hu) hd x
  let w : Fin 5 → Fin n := u ∘ diamondPathVertexIndex r
  have hw : Function.Injective w := hu.comp (diamondPathVertexIndex_injective r)
  let φ : (pathGraph 5) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨w, by
      intro i j hij
      exact (top_adj _ _).mpr (hw.ne ((pathGraph 5).ne_of_adj hij))⟩
  let f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hw⟩
  have hcol (i : Fin 4) :
      (EdgeLabeling.pullback χ f.toHom) (pathFiveEdge i) =
        extendedPathColors (diamondEdgeColors χ u hu) x r i := by
    fin_cases r <;> fin_cases i <;>
      simp [pathFiveEdge, f, φ, w, x, diamondPathVertexIndex,
        extendedPathColors, diamondPathEdgeIndex, diamondEdgeColors,
        EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk, Sym2.eq_swap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  obtain ⟨i, rfl⟩ := pathFiveEdge_surjective e₁
  obtain ⟨j, rfl⟩ := pathFiveEdge_surjective e₂
  have hij : extendedPathColors (diamondEdgeColors χ u hu) x r i =
      extendedPathColors (diamondEdgeColors χ u hu) x r j := by
    simpa only [hcol] using heq
  exact congrArg pathFiveEdge (hr hij)

end ErdosProblems.AntiRamseyPathFiveUpper

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- The complete-graph coloring restricted to a chosen representative. -/
def selectedColor (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : (selectedGraph χ r).edgeSet → Fin q :=
  fun e => χ ⟨e.val, SimpleGraph.edgeSet_mono le_top e.property⟩

theorem selectedColor_injective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : Function.Injective (selectedColor χ r) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₁.property
  have he₂ : e₂.val ∈ Set.range (fun c : Fin q => (r.edge c).val) := by
    rw [← selectedGraph_edgeSet χ r]
    exact e₂.property
  obtain ⟨c₁, hc₁⟩ := he₁
  obtain ⟨c₂, hc₂⟩ := he₂
  have hcolor₁ : selectedColor χ r e₁ = c₁ := by
    have hval : e₁.val = (r.edge c₁).val := hc₁.symm
    simpa [selectedColor, hval] using r.color_eq c₁
  have hcolor₂ : selectedColor χ r e₂ = c₂ := by
    have hval : e₂.val = (r.edge c₂).val := hc₂.symm
    simpa [selectedColor, hval] using r.color_eq c₂
  have hcolors : c₁ = c₂ := hcolor₁.symm.trans (heq.trans hcolor₂)
  apply Subtype.ext
  calc
    e₁.val = (r.edge c₁).val := hc₁.symm
    _ = (r.edge c₂).val := by rw [hcolors]
    _ = e₂.val := hc₂

theorem selectedColor_surjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : Function.Surjective (selectedColor χ r) := by
  intro c
  have hselected : (r.edge c).val ∈ (selectedGraph χ r).edgeSet := by
    rw [selectedGraph_edgeSet]
    exact ⟨c, rfl⟩
  refine ⟨⟨(r.edge c).val, hselected⟩, ?_⟩
  simpa [selectedColor] using r.color_eq c

noncomputable instance selectedGraph_edgeSet_fintype
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ) :
    Fintype (selectedGraph χ r).edgeSet := Fintype.ofFinite _

/-- Every representative choice has exactly one edge per palette color. -/
theorem selectedGraph_card_edgeFinset (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) : (selectedGraph χ r).edgeFinset.card = q := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let equiv : (selectedGraph χ r).edgeSet ≃ Fin q :=
    Equiv.ofBijective (selectedColor χ r)
      ⟨selectedColor_injective χ r, selectedColor_surjective χ r⟩
  simpa using Fintype.card_congr equiv

/-- Any copy in a chosen representative graph becomes a rainbow copy of the
same graph in the complete host graph. -/
theorem copy_in_selectedGraph_isRainbow {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (f : H.Copy (selectedGraph χ r)) :
    IsRainbow ((Copy.ofLE (selectedGraph χ r)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (selectedGraph χ r) (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e = selectedColor χ r (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val = (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact selectedColor_injective χ r
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- No rainbow host copy implies every representative choice is `H.Free`. -/
theorem selectedGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ) :
    H.Free (selectedGraph χ r) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_selectedGraph_isRainbow χ r f)

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.AntiRamseyPathSixK23Transfer

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- The hubs are `u 0,u 1`, the leaves are `u 2,u 3,u 4`, and `u 5`
is the outside vertex. Additional selected edges are allowed. -/
structure RepresentativeK23On {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V) : Prop where
  hub0_b1 : G.Adj (u 0) (u 2)
  hub0_b2 : G.Adj (u 0) (u 3)
  hub0_b3 : G.Adj (u 0) (u 4)
  hub1_b1 : G.Adj (u 1) (u 2)
  hub1_b2 : G.Adj (u 1) (u 3)
  hub1_b3 : G.Adj (u 1) (u 4)

def k23SpokeIndex (i : Fin 6) : Sym2 (Fin 6) :=
  if i = 0 then s(0, 2)
  else if i = 1 then s(0, 3)
  else if i = 2 then s(0, 4)
  else if i = 3 then s(1, 2)
  else if i = 4 then s(1, 3)
  else s(1, 4)

theorem k23SpokeIndex_injective : Function.Injective k23SpokeIndex := by
  decide

theorem k23Spoke_mem {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V)
    (h : RepresentativeK23On G u) (i : Fin 6) :
    Sym2.map u (k23SpokeIndex i) ∈ G.edgeSet := by
  fin_cases i
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b1
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b2
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub0_b3
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b1
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b2
  · simpa [k23SpokeIndex, Sym2.map_mk] using h.hub1_b3

/-- The four rows use spokes `[0,1,4,5]`, `[0,2,5,4]`,
`[3,4,1,2]`, and `[3,5,2,1]` after their common outside chord. -/
def k23ChosenSpokeIndex (r : Fin 4) (i : Fin 4) : Fin 6 :=
  if r = 0 then
    if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else 5
  else if r = 1 then
    if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 5 else 4
  else if r = 2 then
    if i = 0 then 3 else if i = 1 then 4 else if i = 2 then 1 else 2
  else
    if i = 0 then 3 else if i = 1 then 5 else if i = 2 then 2 else 1

theorem k23_choose_avoids {E : Type*}
    (d : Fin 6 → E) (hd : Function.Injective d) (old : E)
    (j : Fin 6) (h : old = d j) (r : Fin 4)
    (hr : ∀ i, j ≠ k23ChosenSpokeIndex r i) :
    ∀ i, old ≠ d (k23ChosenSpokeIndex r i) := by
  intro i
  rw [h]
  exact hd.ne (hr i)

/-- One of four spoke rows avoids an arbitrary edge among six distinct
spokes. The assertion also covers an edge outside the six-spoke set. -/
theorem k23_avoid_one {E : Type*}
    (d : Fin 6 → E) (hd : Function.Injective d) (old : E) :
    ∃ r : Fin 4, ∀ i : Fin 4, old ≠ d (k23ChosenSpokeIndex r i) := by
  classical
  by_cases h0 : old = d 0
  · exact ⟨2, k23_choose_avoids d hd old 0 h0 2 (by decide)⟩
  by_cases h1 : old = d 1
  · exact ⟨1, k23_choose_avoids d hd old 1 h1 1 (by decide)⟩
  by_cases h2 : old = d 2
  · exact ⟨0, k23_choose_avoids d hd old 2 h2 0 (by decide)⟩
  by_cases h3 : old = d 3
  · exact ⟨0, k23_choose_avoids d hd old 3 h3 0 (by decide)⟩
  by_cases h4 : old = d 4
  · exact ⟨3, k23_choose_avoids d hd old 4 h4 3 (by decide)⟩
  by_cases h5 : old = d 5
  · exact ⟨2, k23_choose_avoids d hd old 5 h5 2 (by decide)⟩
  refine ⟨0, ?_⟩
  intro i
  fin_cases i <;> simp_all [k23ChosenSpokeIndex]

/-- Four orders are `w,x,a,y,b,z`, `w,x,a,z,b,y`,
`w,x,b,y,a,z`, and `w,x,b,z,a,y`. -/
def k23OrderIndex (r : Fin 4) (i : Fin 6) : Fin 6 :=
  if i = 0 then 5
  else if i = 1 then 2
  else if r = 0 then
    if i = 2 then 0 else if i = 3 then 3 else if i = 4 then 1 else 4
  else if r = 1 then
    if i = 2 then 0 else if i = 3 then 4 else if i = 4 then 1 else 3
  else if r = 2 then
    if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 0 else 4
  else
    if i = 2 then 1 else if i = 3 then 4 else if i = 4 then 0 else 3

theorem k23OrderIndex_injective (r : Fin 4) :
    Function.Injective (k23OrderIndex r) := by
  fin_cases r <;> decide

theorem k23Path_adj_cases {i j : Fin 6}
    (h : (pathGraph 6).Adj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
    (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
    (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  fin_cases i <;> fin_cases j <;> simp_all [pathGraph_adj]

/-- A selected K₂,₃ on five vertices and a distinct sixth host vertex
force a literal rainbow six-vertex path for every representative choice. -/
theorem rainbow_path_six_of_representative_k23 {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeK23On (selectedGraph χ r) u) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : HostEdge n :=
    ⟨s(u 5, u 2), (top_adj _ _).mpr (hu.ne (by decide))⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  let d : Fin 6 → Sym2 (Fin n) := fun i => Sym2.map u (k23SpokeIndex i)
  have hd : Function.Injective d := by
    intro i j hij
    apply k23SpokeIndex_injective
    apply Sym2.map.injective hu
    simpa [d] using hij
  obtain ⟨row, hrow⟩ := k23_avoid_one d hd old
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hnewSpoke (i : Fin 6) (hne : old ≠ d i) : d i ∈ L'.edgeSet := by
    have he : d i ∈ L.edgeSet := by
      simpa [d, L] using k23Spoke_mem L u h i
    have hed : d i ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact (SimpleGraph.edgeSet_mono hle) hed
  have hchord : L'.Adj (u 5) (u 2) := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  let w : Fin 6 → Fin n := u ∘ k23OrderIndex row
  have hw : Function.Injective w := hu.comp (k23OrderIndex_injective row)
  have hspokeStep (i : Fin 4) :
      L'.Adj (w (Fin.succ (Fin.castSucc i))) (w (Fin.succ (Fin.succ i))) := by
    have hval :
        s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) =
          d (k23ChosenSpokeIndex row i) := by
      fin_cases row <;> fin_cases i <;>
        simp [w, d, k23OrderIndex, k23ChosenSpokeIndex,
          k23SpokeIndex, Sym2.map_mk, Sym2.eq_swap]
    change s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) ∈ L'.edgeSet
    rw [hval]
    exact hnewSpoke (k23ChosenSpokeIndex row i) (hrow i)
  have hstep (i : Fin 5) :
      L'.Adj (w (Fin.castSucc i)) (w (Fin.succ i)) := by
    fin_cases i
    · simpa [w, k23OrderIndex] using hchord
    · simpa using hspokeStep 0
    · simpa using hspokeStep 1
    · simpa using hspokeStep 2
    · simpa using hspokeStep 3
  let φ : (pathGraph 6) →g L' :=
    ⟨w, by
      intro i j hij
      rcases k23Path_adj_cases hij with h01 | h10 | h12 | h21 | h23 |
        h32 | h34 | h43 | h45 | h54
      · rcases h01 with ⟨rfl, rfl⟩
        simpa using hstep 0
      · rcases h10 with ⟨rfl, rfl⟩
        simpa using (hstep 0).symm
      · rcases h12 with ⟨rfl, rfl⟩
        simpa using hstep 1
      · rcases h21 with ⟨rfl, rfl⟩
        simpa using (hstep 1).symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using hstep 2
      · rcases h32 with ⟨rfl, rfl⟩
        simpa using (hstep 2).symm
      · rcases h34 with ⟨rfl, rfl⟩
        simpa using hstep 3
      · rcases h43 with ⟨rfl, rfl⟩
        simpa using (hstep 3).symm
      · rcases h45 with ⟨rfl, rfl⟩
        simpa using hstep 4
      · rcases h54 with ⟨rfl, rfl⟩
        simpa using (hstep 4).symm⟩
  let f : (pathGraph 6).Copy L' := ⟨φ, hw⟩
  refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
  simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

/-- The literal no-rainbow host premise excludes this six-spoke selected
shape for every representative choice. -/
theorem no_representative_k23_of_no_rainbow_path_six {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u : Fin 6 → Fin n) (hu : Function.Injective u) :
    ¬ RepresentativeK23On (selectedGraph χ r) u := by
  intro h
  obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_k23 χ r u hu h
  exact hno f hf

end ErdosProblems.AntiRamseyPathSixK23Transfer

namespace ErdosProblems.PathUpperFinSixExtractor

open SimpleGraph
open ErdosProblems.AntiRamseyPathSixK23Transfer

/-- An eight-edge subgraph of the actual nine-edge two-hub join contains
three common leaves and the distinct fourth leaf, in the existing motif API. -/
theorem representative_k23_of_dense_fin_six_join
    (G H : SimpleGraph (Fin 6)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (hGedges : 8 ≤ G.edgeFinset.card)
    (U : Finset (Fin 6)) (hUcard : U.card = 2)
    (hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧ (u ∈ U ∨ v ∈ U))
    (hHedges : H.edgeFinset.card = 9) :
    ∃ u : Fin 6 → Fin 6, Function.Injective u ∧ RepresentativeK23On G u := by
  classical
  let D := H.edgeFinset \ G.edgeFinset
  have hEdgeSubset : G.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hGH
  have hDsum : D.card + G.edgeFinset.card = 9 := by
    simpa only [D, hHedges] using Finset.card_sdiff_add_card_eq_card hEdgeSubset
  have hDle : D.card ≤ 1 := by omega
  let V : Finset (Fin 6) := Uᶜ
  have hVcard : V.card = 4 := by
    change Uᶜ.card = 4
    simpa only [Fintype.card_fin, hUcard] using Finset.card_compl U
  let Bad := V.filter (fun x => ∃ a ∈ U, ¬ G.Adj a x)
  have hBadSubset : Bad ⊆ V := Finset.filter_subset _ _
  have hMissing (a x : Fin 6) (ha : a ∈ U) (hx : x ∈ V)
      (hnot : ¬ G.Adj a x) : s(a, x) ∈ D := by
    have hxNotU : x ∉ U := Finset.mem_compl.mp hx
    have hax : a ≠ x := by
      intro heq
      exact hxNotU (heq ▸ ha)
    have hHadj : H.Adj a x := (hshape a x).mpr ⟨hax, Or.inl ha⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · exact SimpleGraph.mem_edgeFinset.mpr hHadj
    · intro heG
      exact hnot (SimpleGraph.mem_edgeFinset.mp heG)
  have hBadle : Bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hxV : x ∈ V := (Finset.mem_filter.mp hx).1
    have hyV : y ∈ V := (Finset.mem_filter.mp hy).1
    obtain ⟨a, ha, hax⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨b, hb, hby⟩ := (Finset.mem_filter.mp hy).2
    have heq : s(a, x) = s(b, y) :=
      (Finset.card_le_one.mp hDle) _ (hMissing a x ha hxV hax)
        _ (hMissing b y hb hyV hby)
    rcases Sym2.eq_iff.mp heq with hsame | hswap
    · exact hsame.2
    · exact False.elim ((Finset.mem_compl.mp hyV) (hswap.1 ▸ ha))
  let Good := V \ Bad
  have hGoodV : Good ⊆ V := Finset.sdiff_subset
  have hGoodCard : 3 ≤ Good.card := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hBadSubset
    change Good.card + Bad.card = V.card at hpartition
    omega
  have hSpoke (a x : Fin 6) (ha : a ∈ U) (hx : x ∈ Good) : G.Adj a x := by
    have hxV : x ∈ V := (Finset.mem_sdiff.mp hx).1
    have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
    by_contra hnot
    exact hxNotBad (Finset.mem_filter.mpr ⟨hxV, a, ha, hnot⟩)
  obtain ⟨T, hTGood, hTcard⟩ := Finset.exists_subset_card_eq hGoodCard
  have hTV : T ⊆ V := hTGood.trans hGoodV
  have hRestCard : (V \ T).card = 1 := by
    simpa only [hVcard, hTcard] using Finset.card_sdiff_of_subset hTV
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (V \ T).card)
  have hwV : w ∈ V := (Finset.mem_sdiff.mp hw).1
  have hwNotT : w ∉ T := (Finset.mem_sdiff.mp hw).2
  let hubs : Fin 2 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hUcard).symm i).val
  let leaves : Fin 3 → Fin 6 := fun i => ((Finset.equivFinOfCardEq hTcard).symm i).val
  have hHubsU (i : Fin 2) : hubs i ∈ U :=
    ((Finset.equivFinOfCardEq hUcard).symm i).property
  have hLeavesT (i : Fin 3) : leaves i ∈ T :=
    ((Finset.equivFinOfCardEq hTcard).symm i).property
  have hHubs : Function.Injective hubs := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hUcard).symm.injective
    exact Subtype.ext heq
  have hLeaves : Function.Injective leaves := by
    intro i j heq
    apply (Finset.equivFinOfCardEq hTcard).symm.injective
    exact Subtype.ext heq
  let last : Fin 1 → Fin 6 := fun _ => w
  have hLast : Function.Injective last := fun _i _j _h => Subsingleton.elim _ _
  let tail : Fin 4 → Fin 6 := Fin.append leaves last
  have hTail : Function.Injective tail := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hLeaves, hLast, ?_⟩
    intro i j heq
    have hiw : leaves i = w := heq
    exact hwNotT (hiw ▸ hLeavesT i)
  have hTailV (j : Fin 4) : tail j ∈ V := by
    refine Fin.addCases (m := 3) (n := 1) (fun i => ?_) (fun i => ?_) j
    · simpa only [tail, Fin.append_left] using hTV (hLeavesT i)
    · simpa only [tail, Fin.append_right, last] using hwV
  let u : Fin 6 → Fin 6 := Fin.append hubs tail
  have hu : Function.Injective u := by
    apply Fin.append_injective_iff.mpr
    refine ⟨hHubs, hTail, ?_⟩
    intro i j heq
    exact (Finset.mem_compl.mp (hTailV j)) (heq ▸ hHubsU i)
  have hActualSpoke (i : Fin 2) (j : Fin 3) : G.Adj (hubs i) (leaves j) :=
    hSpoke _ _ (hHubsU i) (hTGood (hLeavesT j))
  refine ⟨u, hu, ?_⟩
  constructor
  · change G.Adj (hubs 0) (leaves 0)
    exact hActualSpoke 0 0
  · change G.Adj (hubs 0) (leaves 1)
    exact hActualSpoke 0 1
  · change G.Adj (hubs 0) (leaves 2)
    exact hActualSpoke 0 2
  · change G.Adj (hubs 1) (leaves 0)
    exact hActualSpoke 1 0
  · change G.Adj (hubs 1) (leaves 1)
    exact hActualSpoke 1 1
  · change G.Adj (hubs 1) (leaves 2)
    exact hActualSpoke 1 2

end ErdosProblems.PathUpperFinSixExtractor

namespace ErdosProblems.PathUpperFinSixJoin

open SimpleGraph
open scoped BigOperators

/-- A noncomplete six-vertex graph with at least eight edges and every
nonuniversal degree at most two is exactly the join of its two actual
universal vertices with the independent complementary four vertices. -/
theorem fin_six_join_of_nonuniversal_degree_cap
    (H : SimpleGraph (Fin 6)) [DecidableRel H.Adj]
    (hneTop : H ≠ ⊤) (hedges : 8 ≤ H.edgeFinset.card)
    (hcap : ∀ x : Fin 6, ¬ H.IsUniversal x → H.degree x ≤ 2) :
    ∃ U : Finset (Fin 6),
      (∀ x, x ∈ U ↔ H.IsUniversal x) ∧ U.card = 2 ∧
      (∀ x, x ∉ U → H.neighborFinset x = U) ∧
      (∀ u v, H.Adj u v ↔ u ≠ v ∧ (u ∈ U ∨ v ∈ U)) ∧
      H.edgeFinset.card = 9 := by
  classical
  let U : Finset (Fin 6) := Finset.univ.filter (fun x => H.IsUniversal x)
  have hmemU (x : Fin 6) : x ∈ U ↔ H.IsUniversal x := by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  have hex : ∃ x : Fin 6, ¬ H.IsUniversal x := by
    by_contra hnone
    apply hneTop
    apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩
  have hsubset (x : Fin 6) (hx : ¬ H.IsUniversal x) :
      U ⊆ H.neighborFinset x := by
    intro y hy
    have hyU : H.IsUniversal y := (hmemU y).mp hy
    have hyx : y ≠ x := by
      intro heq
      subst y
      exact hx hyU
    exact (SimpleGraph.mem_neighborFinset (G := H) (v := x) y).mpr
      (hyU hyx).symm
  obtain ⟨x, hx⟩ := hex
  have hUle : U.card ≤ 2 := by
    calc
      U.card ≤ (H.neighborFinset x).card := Finset.card_le_card (hsubset x hx)
      _ = H.degree x := SimpleGraph.card_neighborFinset_eq_degree H x
      _ ≤ 2 := hcap x hx
  have hUdegree (x : Fin 6) (hx : x ∈ U) : H.degree x = 5 := by
    simpa only [Fintype.card_fin] using
      (SimpleGraph.degree_eq_card_sub_one (G := H) x).mpr ((hmemU x).mp hx)
  have hNUdegree (x : Fin 6) (hx : x ∈ Uᶜ) : H.degree x ≤ 2 := by
    apply hcap x
    intro hxU
    exact (Finset.mem_compl.mp hx) ((hmemU x).mpr hxU)
  have hsumU : (∑ x ∈ U, H.degree x) = U.card * 5 :=
    Finset.sum_const_nat hUdegree
  have hsumNU : (∑ x ∈ Uᶜ, H.degree x) ≤ Uᶜ.card * 2 := by
    calc
      (∑ x ∈ Uᶜ, H.degree x) ≤ ∑ _x ∈ Uᶜ, (2 : ℕ) :=
        Finset.sum_le_sum hNUdegree
      _ = Uᶜ.card * 2 := Finset.sum_const_nat (fun _x _hx => rfl)
  have hcomplCard : Uᶜ.card = 6 - U.card := by
    simpa only [Fintype.card_fin] using Finset.card_compl U
  have hsplit := Finset.sum_compl_add_sum U (fun v => H.degree v)
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges H
  have hUcard : U.card = 2 := by omega
  have hneighbors (x : Fin 6) (hx : x ∉ U) : H.neighborFinset x = U := by
    have hxNU : ¬ H.IsUniversal x := fun hxU => hx ((hmemU x).mpr hxU)
    have hEq : U = H.neighborFinset x :=
      Finset.eq_of_subset_of_card_le (hsubset x hxNU) (by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hUcard]
        exact hcap x hxNU)
    exact hEq.symm
  have hNUdegreeExact (x : Fin 6) (hx : x ∈ Uᶜ) : H.degree x = 2 := by
    have hc := congrArg Finset.card (hneighbors x (Finset.mem_compl.mp hx))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree, hUcard] using hc
  have hsumNUExact : (∑ x ∈ Uᶜ, H.degree x) = Uᶜ.card * 2 :=
    Finset.sum_const_nat hNUdegreeExact
  have hcount : H.edgeFinset.card = 9 := by omega
  have hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧ (u ∈ U ∨ v ∈ U) := by
    intro u v
    constructor
    · intro hadj
      refine ⟨hadj.ne, ?_⟩
      by_cases hu : u ∈ U
      · exact Or.inl hu
      · apply Or.inr
        rw [← hneighbors u hu]
        exact (SimpleGraph.mem_neighborFinset (G := H) (v := u) v).mpr hadj
    · rintro ⟨huv, hu | hv⟩
      · exact ((hmemU u).mp hu) huv
      · exact (((hmemU v).mp hv) huv.symm).symm
  exact ⟨U, hmemU, hUcard, hneighbors, hshape, hcount⟩

end ErdosProblems.PathUpperFinSixJoin

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

theorem edge_count_le_complement_clique_and_slots
    {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (L : Finset (Fin k)) (a : ℕ) (hL : ∀ x ∈ L, H.degree x ≤ a) :
    H.edgeFinset.card ≤ (k - L.card).choose 2 + L.card * a := by
  classical
  let C : Finset (Fin k) := Lᶜ
  let inside := H.edgeFinset.filter (fun e => e.toFinset ⊆ C)
  let touching := L.biUnion (fun v => H.incidenceFinset v)
  have hcover : H.edgeFinset ⊆ inside ∪ touching := by
    intro e he
    by_cases hinside : e.toFinset ⊆ C
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hinside⟩))
    · have hex : ∃ x, x ∈ e.toFinset ∧ x ∈ L := by
        by_contra hnone
        apply hinside
        intro x hx
        apply Finset.mem_compl.mpr
        intro hxL
        exact hnone ⟨x, hx, hxL⟩
      obtain ⟨x, hx, hxL⟩ := hex
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨x, hxL, ?_⟩
      rw [H.incidenceFinset_eq_filter x]
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_toFinset.mp hx⟩
  have hinsideCount : inside.card ≤ C.card.choose 2 := by
    change (H.edgeFinset.filter (fun e => e.toFinset ⊆ C)).card ≤ C.card.choose 2
    rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := H) C]
    have hCfin : Fintype.card {v : Fin k // v ∈ (↑C : Set (Fin k))} = C.card :=
      Fintype.card_of_subtype C (by intro v; rfl)
    simpa only [hCfin] using
      (SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := H.induce (↑C : Set (Fin k))))
  have htouchingCount : touching.card ≤ L.card * a := by
    apply Finset.card_biUnion_le_card_mul L (fun v => H.incidenceFinset v) a
    intro x hx
    simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hL x hx
  have hCcard : C.card = k - L.card := by
    simpa only [Fintype.card_fin] using Finset.card_compl L
  calc
    H.edgeFinset.card ≤ (inside ∪ touching).card := Finset.card_le_card hcover
    _ ≤ inside.card + touching.card := Finset.card_union_le inside touching
    _ ≤ C.card.choose 2 + L.card * a := Nat.add_le_add hinsideCount htouchingCount
    _ = (k - L.card).choose 2 + L.card * a := by rw [hCcard]

/-- A connected noncomplete spanning graph with the missing-pair degree
closure has an actual low-degree set and the corresponding edge-count cap. -/
theorem spanning_degree_slots_and_edge_count
    (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hneTop : H ≠ ⊤)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2) :
    ∃ (a : ℕ) (L : Finset (Fin k)),
      1 ≤ a ∧ 2 * a ≤ k - 2 ∧ L.card = a + 1 ∧
      (∀ x ∈ L, H.degree x ≤ a) ∧
      H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) := by
  classical
  let N : Finset (Fin k) := Finset.univ.filter (fun v => ¬ H.IsUniversal v)
  have hN : N.Nonempty := by
    by_contra hnone
    apply hneTop
    apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
    intro x
    by_contra hx
    apply hnone
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨v, hvN, hmaxv⟩ := Finset.exists_max_image N (fun v => H.degree v) hN
  have hvNU : ¬ H.IsUniversal v := (Finset.mem_filter.mp hvN).2
  let T := Hᶜ.neighborFinset v
  have hTcard : T.card = k - 1 - H.degree v := by
    change (Hᶜ.neighborFinset v).card = k - 1 - H.degree v
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree_compl,
      Fintype.card_fin]
  have hbLt : H.degree v < k - 1 := by
    simpa only [Fintype.card_fin] using
      (SimpleGraph.degree_lt_card_sub_one (G := H) v).mpr hvNU
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, huT, hmaxu⟩ := Finset.exists_max_image T (fun v => H.degree v) hT
  have hcompl : Hᶜ.Adj v u :=
    (SimpleGraph.mem_neighborFinset (G := Hᶜ) (v := v) u).mp huT
  obtain ⟨hvu, hmissing⟩ := (SimpleGraph.compl_adj H v u).mp hcompl
  have huNU : ¬ H.IsUniversal u := by
    intro hu
    exact hmissing (hu hvu.symm).symm
  have huN : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ u, huNU⟩
  let a := H.degree u
  have haLeB : a ≤ H.degree v := hmaxv u huN
  have hsum : a + H.degree v ≤ k - 2 := by
    have := hclosure v u hvu hmissing
    dsimp only [a]
    omega
  have haPos : 1 ≤ a := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hvu.symm (hconn u v)
    exact hpos
  have htwo : 2 * a ≤ k - 2 := by omega
  have hk2 : 2 ≤ k := by omega
  have hsumAmbient : a + H.degree v + 2 ≤ k := by
    have h := Nat.add_le_add_right hsum 2
    rw [Nat.sub_add_cancel hk2] at h
    exact h
  have hsize : a + 1 ≤ T.card := by omega
  obtain ⟨L, hLT, hLcard⟩ := Finset.exists_subset_card_eq hsize
  have hLdegree : ∀ x ∈ L, H.degree x ≤ a := by
    intro x hx
    exact hmaxu x (hLT hx)
  have hcount := edge_count_le_complement_clique_and_slots H L a hLdegree
  have hshift : k - (a + 1) = k - 1 - a := by omega
  have hbound : H.edgeFinset.card ≤ (k - 1 - a).choose 2 + a * (a + 1) := by
    simpa only [hLcard, hshift, Nat.mul_comm] using hcount
  exact ⟨a, L, haPos, htwo, hLcard, hLdegree, hbound⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

theorem degree_slot_cap_lt_spanning_threshold
    (k a : ℕ) (hk : 11 ≤ k) (ha : 1 ≤ a) (haStrict : 2 ≤ a)
    (haBound : 2 * a ≤ k - 2) :
    (k - 1 - a).choose 2 + a * (a + 1) < (k - 2).choose 2 + 2 := by
  let T := (k - 2).choose 2 + 2
  let h := (k - 1 - a).choose 2 + a * (a + 1)
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : 3 ≤ k := by omega
  have ha1 : a ≤ k - 1 := by omega
  have ha2 : a ≤ k - 2 := by omega
  have h3a : 3 * a ≤ 2 * k := by omega
  have h8 : 8 ≤ 2 * k - 3 * a := by omega
  have hfactor : 1 ≤ 2 * k - 3 * a - 8 := by omega
  have hshiftT : k - 3 + 1 = k - 2 := by omega
  have hshiftH : k - 2 - a + 1 = k - 1 - a := by omega
  have hchooseT :
      (k - 2) * (k - 3) = (k - 2).choose 2 * 2 := by
    simpa only [Nat.choose_one_right, hshiftT] using
      Nat.add_one_mul_choose_eq (k - 3) 1
  have hchooseH :
      (k - 1 - a) * (k - 2 - a) = (k - 1 - a).choose 2 * 2 := by
    simpa only [Nat.choose_one_right, hshiftH] using
      Nat.add_one_mul_choose_eq (k - 2 - a) 1
  have hcastT : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 :=
    Nat.cast_sub hk2
  have hcastTpred : ((k - 3 : ℕ) : ℤ) = (k : ℤ) - 3 :=
    Nat.cast_sub hk3
  have hcastH : ((k - 1 - a : ℕ) : ℤ) = (k : ℤ) - 1 - (a : ℤ) := by
    simp only [Nat.cast_sub ha1, Nat.cast_sub hk1, Nat.cast_one]
  have hcastHpred : ((k - 2 - a : ℕ) : ℤ) = (k : ℤ) - 2 - (a : ℤ) := by
    simp only [Nat.cast_sub ha2, Nat.cast_sub hk2, Nat.cast_ofNat]
  have hcastA : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 :=
    Nat.cast_sub ha
  have hcastFactor :
      ((2 * k - 3 * a - 8 : ℕ) : ℤ) =
        2 * (k : ℤ) - 3 * (a : ℤ) - 8 := by
    simp only [Nat.cast_sub h8, Nat.cast_sub h3a, Nat.cast_mul,
      Nat.cast_ofNat]
  have hcT :
      ((k - 2 : ℕ) : ℤ) * ((k - 3 : ℕ) : ℤ) =
        ((k - 2).choose 2 : ℤ) * 2 := by
    exact_mod_cast hchooseT
  have hcH :
      ((k - 1 - a : ℕ) : ℤ) * ((k - 2 - a : ℕ) : ℤ) =
        ((k - 1 - a).choose 2 : ℤ) * 2 := by
    exact_mod_cast hchooseH
  rw [hcastT, hcastTpred] at hcT
  rw [hcastH, hcastHpred] at hcH
  have hidentityInt :
      2 * (T : ℤ) = 2 * (h : ℤ) +
        (((a - 1) * (2 * k - 3 * a - 8) : ℕ) : ℤ) := by
    dsimp only [T, h]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, hcastA, hcastFactor]
    nlinarith [hcT, hcH]
  have hidentity :
      2 * T = 2 * h + (a - 1) * (2 * k - 3 * a - 8) := by
    exact_mod_cast hidentityInt
  have hgap : 0 < (a - 1) * (2 * k - 3 * a - 8) :=
    Nat.mul_pos (by omega) (by omega)
  change h < T
  omega

/-- A connected dense spanning graph satisfying the missing-pair degree closure
is complete at every order at least11, with minimum degree at least2. -/
theorem connected_spanning_dense_closed_eq_top
    (k : ℕ) (hk : 11 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected) (hmin : ∀ v, 2 ≤ H.degree v)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) : H = ⊤ := by
  classical
  by_contra hneTop
  obtain ⟨a, L, ha, haBound, hLcard, hLdeg, hcount⟩ :=
    spanning_degree_slots_and_edge_count k (by omega) H hconn hneTop hclosure
  have hLnonempty : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hLnonempty
  have haStrict : 2 ≤ a := (hmin x).trans (hLdeg x hx)
  have hstrict := degree_slot_cap_lt_spanning_threshold k a hk ha haStrict haBound
  exact (not_lt_of_ge (hedges.trans hcount)) hstrict

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- Retain the actual induced-complement count, rather than replacing it with
its clique cap. This is the equality information needed from the edge cover. -/
theorem edge_count_le_induced_complement_and_slots
    {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (L : Finset (Fin k)) (a : ℕ) (hL : ∀ x ∈ L, H.degree x ≤ a) :
    H.edgeFinset.card ≤ (H.induce (↑(Lᶜ) : Set (Fin k))).edgeFinset.card +
      L.card * a := by
  classical
  let C : Finset (Fin k) := Lᶜ
  let inside := H.edgeFinset.filter (fun e => e.toFinset ⊆ C)
  let touching := L.biUnion (fun v => H.incidenceFinset v)
  have hcover : H.edgeFinset ⊆ inside ∪ touching := by
    intro e he
    by_cases hinside : e.toFinset ⊆ C
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hinside⟩))
    · have hex : ∃ x, x ∈ e.toFinset ∧ x ∈ L := by
        by_contra hnone
        apply hinside
        intro x hx
        apply Finset.mem_compl.mpr
        intro hxL
        exact hnone ⟨x, hx, hxL⟩
      obtain ⟨x, hx, hxL⟩ := hex
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨x, hxL, ?_⟩
      rw [H.incidenceFinset_eq_filter x]
      exact Finset.mem_filter.mpr ⟨he, Sym2.mem_toFinset.mp hx⟩
  have hinsideCount : inside.card = (H.induce (↑C : Set (Fin k))).edgeFinset.card :=
    SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := H) C
  have htouchingCount : touching.card ≤ L.card * a := by
    apply Finset.card_biUnion_le_card_mul L (fun v => H.incidenceFinset v) a
    intro x hx
    simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hL x hx
  calc
    H.edgeFinset.card ≤ (inside ∪ touching).card := Finset.card_le_card hcover
    _ ≤ inside.card + touching.card := Finset.card_union_le inside touching
    _ ≤ inside.card + L.card * a := Nat.add_le_add_left htouchingCount inside.card
    _ = (H.induce (↑(Lᶜ) : Set (Fin k))).edgeFinset.card + L.card * a := by
      rw [hinsideCount]

/-- At order at least11, a connected closed spanning path-free graph at the
threshold is exactly a complete remainder with two degree1 leaves at one hub.
This is an ordinary graph saturation result; it supplies no color-owner claim. -/
theorem connected_spanning_dense_closed_is_s1
    (k : ℕ) (hk : 11 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (hfree : (pathGraph k).Free H)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) :
    ∃ (L : Finset (Fin k)) (w : Fin k),
      L.card = 2 ∧ w ∉ L ∧ (∀ x ∈ L, H.degree x = 1) ∧
      H.edgeFinset.card = (k - 2).choose 2 + 2 ∧
      H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ ∧
      (∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y) ∧
      (∀ u v, H.Adj u v ↔ u ≠ v ∧
        ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = w) ∨ (v ∈ L ∧ u = w))) := by
  classical
  have hneTop : H ≠ ⊤ := by
    intro heq
    apply hfree
    rw [heq]
    exact ⟨Copy.ofLE (pathGraph k) ⊤ le_top⟩
  obtain ⟨a, L, ha, haBound, hLcard, hLdeg, hcount⟩ :=
    spanning_degree_slots_and_edge_count k (by omega) H hconn hneTop hclosure
  have haOne : a = 1 := by
    by_contra hne
    have haStrict : 2 ≤ a := by omega
    have hstrict := degree_slot_cap_lt_spanning_threshold k a hk ha haStrict haBound
    exact (not_lt_of_ge (hedges.trans hcount)) hstrict
  subst a
  have hLcardTwo : L.card = 2 := by omega
  have hshift : k - 1 - 1 = k - 2 := by omega
  have hcountThreshold : H.edgeFinset.card ≤ (k - 2).choose 2 + 2 := by
    simpa [hshift] using hcount
  have hcountExact : H.edgeFinset.card = (k - 2).choose 2 + 2 :=
    Nat.le_antisymm hcountThreshold hedges
  obtain ⟨x0, y0, hxy, hLpair⟩ := Finset.card_eq_two.mp hLcardTwo
  have hx0 : x0 ∈ L := by rw [hLpair]; simp
  have hy0 : y0 ∈ L := by rw [hLpair]; simp
  have hxDegree : H.degree x0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy (hconn x0 y0)
    have hle := hLdeg x0 hx0
    omega
  have hyDegree : H.degree y0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy.symm (hconn y0 x0)
    have hle := hLdeg y0 hy0
    omega
  have hLdegree : ∀ x ∈ L, H.degree x = 1 := by
    intro x hx
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · exact hxDegree
    · exact hyDegree
  let C : Finset (Fin k) := Lᶜ
  let K := H.induce (↑C : Set (Fin k))
  have hCcard : C.card = k - 2 := by
    simpa only [Fintype.card_fin, hLcardTwo] using Finset.card_compl L
  have hcoreCover : H.edgeFinset.card ≤ K.edgeFinset.card + 2 := by
    simpa only [hLcardTwo, Nat.mul_one] using
      edge_count_le_induced_complement_and_slots H L 1 hLdeg
  have hcoreCount : (k - 2).choose 2 ≤ K.edgeFinset.card := by omega
  have htopCount : (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset.card = (k - 2).choose 2 := by
    simpa only [Fintype.card_coe, hCcard] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := {v : Fin k // v ∈ C}))
  have hcoreEdges : K.edgeFinset = (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
      (by rw [htopCount]; exact hcoreCount)
  have hcoreTop : H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ :=
    SimpleGraph.edgeFinset_inj.mp hcoreEdges
  have hleavesNotAdj : ¬ H.Adj x0 y0 := by
    intro hadj
    obtain ⟨nx, _hnx, hnxUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
    obtain ⟨ny, _hny, hnyUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
    have hclosed : ∀ u ∈ L, ∀ v, H.Adj u v → v ∈ L := by
      intro u hu v huv
      have hmem : u = x0 ∨ u = y0 := by simpa [hLpair] using hu
      rcases hmem with rfl | rfl
      · have hv : v = y0 := (hnxUnique v huv).trans (hnxUnique y0 hadj).symm
        exact hv.symm ▸ hy0
      · have hv : v = x0 := (hnyUnique v huv).trans (hnyUnique x0 hadj.symm).symm
        exact hv.symm ▸ hx0
    have hstay : ∀ {u v : Fin k}, H.Walk u v → u ∈ L → v ∈ L := by
      intro u v p
      induction p with
      | nil => exact fun hu => hu
      | cons huv _ ih => exact fun hu => ih (hclosed _ hu _ huv)
    have hLuniv : L = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun v => hstay (hconn x0 v).some hx0)
    have hcard : L.card = k := by rw [hLuniv, Finset.card_univ, Fintype.card_fin]
    omega
  have hLindependent : ∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y := by
    intro x hx y hy
    have hxm : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    have hym : y = x0 ∨ y = y0 := by simpa [hLpair] using hy
    rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
    · exact H.loopless.irrefl _
    · exact hleavesNotAdj
    · exact fun hadj => hleavesNotAdj hadj.symm
    · exact H.loopless.irrefl _
  have hcoreAdj : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → H.Adj u v := by
    intro u hu v hv huv
    have hsubNe : (⟨u, hu⟩ : {v : Fin k // v ∈ C}) ≠ ⟨v, hv⟩ := by
      intro heq
      exact huv (congrArg Subtype.val heq)
    have htop : K = ⊤ := hcoreTop
    have hadj : K.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [htop]
      exact (SimpleGraph.top_adj _ _).mpr hsubNe
    exact hadj
  obtain ⟨p, hxp, hpUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
  obtain ⟨q, hyq, hqUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
  have hpNotL : p ∉ L := by
    intro hpL
    exact hLindependent x0 hx0 p hpL hxp
  have hqNotL : q ∉ L := by
    intro hqL
    exact hLindependent y0 hy0 q hqL hyq
  have hqC : q ∈ C := Finset.mem_compl.mpr hqNotL
  have hsameHub : p = q := by
    by_contra hpq
    have hxq : x0 ≠ q := by
      intro heq
      exact hqNotL (heq ▸ hx0)
    have hmissing : ¬ H.Adj x0 q := by
      intro hadj
      exact hpq (hpUnique q hadj).symm
    have hyNotErase : y0 ∉ C.erase q := by
      intro hy
      exact (Finset.mem_compl.mp (Finset.mem_erase.mp hy).2) hy0
    let N := insert y0 (C.erase q)
    have hNcard : N.card = k - 2 := by
      change (insert y0 (C.erase q)).card = k - 2
      rw [Finset.card_insert_of_notMem hyNotErase, Finset.card_erase_of_mem hqC,
        hCcard]
      omega
    have hNsubset : N ⊆ H.neighborFinset q := by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hyq.symm
      · exact hcoreAdj q hqC v (Finset.mem_erase.mp hv).2
          (Finset.mem_erase.mp hv).1.symm
    have hqLower : k - 2 ≤ H.degree q := by
      calc
        k - 2 = N.card := hNcard.symm
        _ ≤ (H.neighborFinset q).card := Finset.card_le_card hNsubset
        _ = H.degree q := SimpleGraph.card_neighborFinset_eq_degree H q
    have hclosedPair := hclosure x0 q hxq hmissing
    omega
  have hleafAdj : ∀ x ∈ L, ∀ v, H.Adj x v ↔ v = p := by
    intro x hx v
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · constructor
      · exact hpUnique v
      · intro hv
        exact hv.symm ▸ hxp
    · constructor
      · intro hadj
        exact (hqUnique v hadj).trans hsameHub.symm
      · intro hv
        have hyp := hsameHub.symm ▸ hyq
        exact hv.symm ▸ hyp
  have hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧
      ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = p) ∨ (v ∈ L ∧ u = p)) := by
    intro u v
    constructor
    · intro hadj
      refine ⟨hadj.ne, ?_⟩
      by_cases hu : u ∈ L
      · exact Or.inr (Or.inl ⟨hu, (hleafAdj u hu v).mp hadj⟩)
      · by_cases hv : v ∈ L
        · exact Or.inr (Or.inr ⟨hv, (hleafAdj v hv u).mp hadj.symm⟩)
        · exact Or.inl ⟨hu, hv⟩
    · rintro ⟨huv, hcase⟩
      rcases hcase with ⟨hu, hv⟩ | ⟨hu, hvp⟩ | ⟨hv, hup⟩
      · exact hcoreAdj u (Finset.mem_compl.mpr hu) v (Finset.mem_compl.mpr hv) huv
      · exact (hleafAdj u hu v).mpr hvp
      · exact ((hleafAdj v hv u).mpr hup).symm
  exact ⟨L, p, hLcardTwo, hpNotL, hLdegree, hcountExact, hcoreTop, hLindependent, hshape⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

/-- An actual two-vertex slot of degree at most1 at the original edge threshold
forces a complete remainder and two degree1 leaves at one actual hub. -/
theorem a_one_slots_force_s1
    (k : ℕ) (hk : 5 ≤ k) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hclosure : ∀ u v : Fin k, u ≠ v → ¬ H.Adj u v →
      H.degree u + H.degree v ≤ k - 2)
    (L : Finset (Fin k)) (hLcardTwo : L.card = 2)
    (hLdeg : ∀ x ∈ L, H.degree x ≤ 1)
    (hedges : (k - 2).choose 2 + 2 ≤ H.edgeFinset.card) :
    ∃ w : Fin k,
      w ∉ L ∧ (∀ x ∈ L, H.degree x = 1) ∧
      H.edgeFinset.card = (k - 2).choose 2 + 2 ∧
      H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ ∧
      (∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y) ∧
      (∀ u v, H.Adj u v ↔ u ≠ v ∧
        ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = w) ∨ (v ∈ L ∧ u = w))) := by
  classical
  obtain ⟨x0, y0, hxy, hLpair⟩ := Finset.card_eq_two.mp hLcardTwo
  have hx0 : x0 ∈ L := by rw [hLpair]; simp
  have hy0 : y0 ∈ L := by rw [hLpair]; simp
  have hxDegree : H.degree x0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy (hconn x0 y0)
    have hle := hLdeg x0 hx0
    omega
  have hyDegree : H.degree y0 = 1 := by
    have hpos := SimpleGraph.Reachable.degree_pos_left hxy.symm (hconn y0 x0)
    have hle := hLdeg y0 hy0
    omega
  have hLdegree : ∀ x ∈ L, H.degree x = 1 := by
    intro x hx
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · exact hxDegree
    · exact hyDegree
  let C : Finset (Fin k) := Lᶜ
  let K := H.induce (↑C : Set (Fin k))
  have hCcard : C.card = k - 2 := by
    simpa only [Fintype.card_fin, hLcardTwo] using Finset.card_compl L
  have hcoreCover : H.edgeFinset.card ≤ K.edgeFinset.card + 2 := by
    simpa only [hLcardTwo, Nat.mul_one] using
      edge_count_le_induced_complement_and_slots H L 1 hLdeg
  have hcoreCount : (k - 2).choose 2 ≤ K.edgeFinset.card := by omega
  have htopCount : (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset.card = (k - 2).choose 2 := by
    simpa only [Fintype.card_coe, hCcard] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := {v : Fin k // v ∈ C}))
  have hcoreEdges : K.edgeFinset = (⊤ : SimpleGraph {v : Fin k // v ∈ C}).edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le_top)
      (by rw [htopCount]; exact hcoreCount)
  have hcoreTop : H.induce (↑(Lᶜ) : Set (Fin k)) = ⊤ :=
    SimpleGraph.edgeFinset_inj.mp hcoreEdges
  have hKcount : K.edgeFinset.card = (k - 2).choose 2 :=
    (congrArg Finset.card hcoreEdges).trans htopCount
  have hcountExact : H.edgeFinset.card = (k - 2).choose 2 + 2 := by omega
  have hleavesNotAdj : ¬ H.Adj x0 y0 := by
    intro hadj
    obtain ⟨nx, _hnx, hnxUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
    obtain ⟨ny, _hny, hnyUnique⟩ :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
    have hclosed : ∀ u ∈ L, ∀ v, H.Adj u v → v ∈ L := by
      intro u hu v huv
      have hmem : u = x0 ∨ u = y0 := by simpa [hLpair] using hu
      rcases hmem with rfl | rfl
      · have hv : v = y0 := (hnxUnique v huv).trans (hnxUnique y0 hadj).symm
        exact hv.symm ▸ hy0
      · have hv : v = x0 := (hnyUnique v huv).trans (hnyUnique x0 hadj.symm).symm
        exact hv.symm ▸ hx0
    have hstay : ∀ {u v : Fin k}, H.Walk u v → u ∈ L → v ∈ L := by
      intro u v p
      induction p with
      | nil => exact fun hu => hu
      | cons huv _ ih => exact fun hu => ih (hclosed _ hu _ huv)
    have hLuniv : L = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun v => hstay (hconn x0 v).some hx0)
    have hcard : L.card = k := by rw [hLuniv, Finset.card_univ, Fintype.card_fin]
    omega
  have hLindependent : ∀ x ∈ L, ∀ y ∈ L, ¬ H.Adj x y := by
    intro x hx y hy
    have hxm : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    have hym : y = x0 ∨ y = y0 := by simpa [hLpair] using hy
    rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
    · exact H.loopless.irrefl _
    · exact hleavesNotAdj
    · exact fun hadj => hleavesNotAdj hadj.symm
    · exact H.loopless.irrefl _
  have hcoreAdj : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → H.Adj u v := by
    intro u hu v hv huv
    have hsubNe : (⟨u, hu⟩ : {v : Fin k // v ∈ C}) ≠ ⟨v, hv⟩ := by
      intro heq
      exact huv (congrArg Subtype.val heq)
    have htop : K = ⊤ := hcoreTop
    have hadj : K.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [htop]
      exact (SimpleGraph.top_adj _ _).mpr hsubNe
    exact hadj
  obtain ⟨p, hxp, hpUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hxDegree
  obtain ⟨q, hyq, hqUnique⟩ :=
    SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hyDegree
  have hpNotL : p ∉ L := by
    intro hpL
    exact hLindependent x0 hx0 p hpL hxp
  have hqNotL : q ∉ L := by
    intro hqL
    exact hLindependent y0 hy0 q hqL hyq
  have hqC : q ∈ C := Finset.mem_compl.mpr hqNotL
  have hsameHub : p = q := by
    by_contra hpq
    have hxq : x0 ≠ q := by
      intro heq
      exact hqNotL (heq ▸ hx0)
    have hmissing : ¬ H.Adj x0 q := by
      intro hadj
      exact hpq (hpUnique q hadj).symm
    have hyNotErase : y0 ∉ C.erase q := by
      intro hy
      exact (Finset.mem_compl.mp (Finset.mem_erase.mp hy).2) hy0
    let N := insert y0 (C.erase q)
    have hNcard : N.card = k - 2 := by
      change (insert y0 (C.erase q)).card = k - 2
      rw [Finset.card_insert_of_notMem hyNotErase, Finset.card_erase_of_mem hqC,
        hCcard]
      omega
    have hNsubset : N ⊆ H.neighborFinset q := by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hyq.symm
      · exact hcoreAdj q hqC v (Finset.mem_erase.mp hv).2
          (Finset.mem_erase.mp hv).1.symm
    have hqLower : k - 2 ≤ H.degree q := by
      calc
        k - 2 = N.card := hNcard.symm
        _ ≤ (H.neighborFinset q).card := Finset.card_le_card hNsubset
        _ = H.degree q := SimpleGraph.card_neighborFinset_eq_degree H q
    have hclosedPair := hclosure x0 q hxq hmissing
    omega
  have hleafAdj : ∀ x ∈ L, ∀ v, H.Adj x v ↔ v = p := by
    intro x hx v
    have hmem : x = x0 ∨ x = y0 := by simpa [hLpair] using hx
    rcases hmem with rfl | rfl
    · constructor
      · exact hpUnique v
      · intro hv
        exact hv.symm ▸ hxp
    · constructor
      · intro hadj
        exact (hqUnique v hadj).trans hsameHub.symm
      · intro hv
        have hyp := hsameHub.symm ▸ hyq
        exact hv.symm ▸ hyp
  have hshape : ∀ u v, H.Adj u v ↔ u ≠ v ∧
      ((u ∉ L ∧ v ∉ L) ∨ (u ∈ L ∧ v = p) ∨ (v ∈ L ∧ u = p)) := by
    intro u v
    constructor
    · intro hadj
      refine ⟨hadj.ne, ?_⟩
      by_cases hu : u ∈ L
      · exact Or.inr (Or.inl ⟨hu, (hleafAdj u hu v).mp hadj⟩)
      · by_cases hv : v ∈ L
        · exact Or.inr (Or.inr ⟨hv, (hleafAdj v hv u).mp hadj.symm⟩)
        · exact Or.inl ⟨hu, hv⟩
    · rintro ⟨huv, hcase⟩
      rcases hcase with ⟨hu, hv⟩ | ⟨hu, hvp⟩ | ⟨hv, hup⟩
      · exact hcoreAdj u (Finset.mem_compl.mpr hu) v (Finset.mem_compl.mpr hv) huv
      · exact (hleafAdj u hu v).mpr hvp
      · exact ((hleafAdj v hv u).mpr hup).symm
  exact ⟨p, hpNotL, hLdegree, hcountExact, hcoreTop, hLindependent, hshape⟩

end ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathCliqueLower

theorem two_incident_nat {m i j : ℕ}
    (hm : 2 ≤ m) (hi : i < m + 1) (hj : j < m + 1) (hij : i < j) :
    ∃ p q : ℕ, p < m ∧ q < m ∧ p ≠ q ∧
      (i = p ∨ i = p + 1 ∨ j = p ∨ j = p + 1) ∧
      (i = q ∨ i = q + 1 ∨ j = q ∨ j = q + 1) := by
  by_cases hsep : i + 1 < j
  · refine ⟨i, j - 1, by omega, by omega, by omega, ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  · have hnext : j = i + 1 := by omega
    by_cases hi0 : i = 0
    · refine ⟨0, 1, by omega, by omega, by omega, ?_, ?_⟩
      · exact Or.inl hi0
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · refine ⟨i - 1, i, by omega, by omega, by omega, ?_, ?_⟩
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inl rfl

/-- Two distinct vertices of a path of order `m + 1`, with `m ≥ 2`, touch at
least two different consecutive-index edges. -/
theorem two_incident_path_edges_succ {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    ∃ p q : Fin m, p ≠ q ∧
      (i = p.castSucc ∨ i = p.succ ∨ j = p.castSucc ∨ j = p.succ) ∧
      (i = q.castSucc ∨ i = q.succ ∨ j = q.castSucc ∨ j = q.succ) := by
  have hlift (a b : Fin (m + 1)) (hab : a < b) :
      ∃ p q : Fin m, p ≠ q ∧
        (a = p.castSucc ∨ a = p.succ ∨ b = p.castSucc ∨ b = p.succ) ∧
        (a = q.castSucc ∨ a = q.succ ∨ b = q.castSucc ∨ b = q.succ) := by
    obtain ⟨p, q, hp, hq, hpq, hincp, hincq⟩ :=
      two_incident_nat hm a.isLt b.isLt hab
    refine ⟨⟨p, hp⟩, ⟨q, hq⟩, ?_, ?_, ?_⟩
    · intro he
      have hv := congrArg Fin.val he
      exact hpq hv
    · simpa [Fin.ext_iff] using hincp
    · simpa [Fin.ext_iff] using hincq
  rcases lt_trichotomy i j with h | h | h
  · exact hlift i j h
  · exact False.elim (hij h)
  · obtain ⟨p, q, hpq, hincp, hincq⟩ := hlift j i h
    refine ⟨p, q, hpq, ?_, ?_⟩ <;> tauto

/-- An injective placement of `r + 2` vertices into `Fin n` has at least two
vertices outside the first `r` values. -/
theorem two_vertices_outside_prefix {r n : ℕ}
    (f : Fin (r + 2) → Fin n) (hf : Function.Injective f) :
    ∃ i j : Fin (r + 2), i ≠ j ∧ r ≤ (f i).val ∧ r ≤ (f j).val := by
  classical
  let S : Finset (Fin (r + 2)) := Finset.univ.filter (fun i => (f i).val < r)
  let T : Finset (Fin (r + 2)) := Finset.univ.filter (fun i => ¬ (f i).val < r)
  have hS : S.card ≤ r := by
    let g : S → Fin r := fun i => ⟨(f i.1).val, (Finset.mem_filter.mp i.2).2⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply hf
      apply Fin.ext
      change (⟨(f a.1).val, _⟩ : Fin r) = ⟨(f b.1).val, _⟩ at hab
      exact congrArg (fun t : Fin r => t.val) hab
    simpa using Fintype.card_le_of_injective g hg
  have hsum : S.card + T.card = r + 2 := by
    simpa [S, T] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin (r + 2) => (f i).val < r))
  have hT : 1 < T.card := by omega
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hT
  refine ⟨i, j, hij, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
  · exact Nat.le_of_not_gt (Finset.mem_filter.mp hj).2

end ErdosProblems.PathCliqueLower

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

def pathEdgeGeneral (r : ℕ) (p : Fin (r + 1)) : (pathGraph (r + 2)).edgeSet :=
  ⟨s(p.castSucc, p.succ), by
    rw [mem_edgeSet]
    apply pathGraph_adj.mpr
    left
    simp⟩

theorem pathEdgeGeneral_injective (r : ℕ) :
    Function.Injective (pathEdgeGeneral r) := by
  intro p q he
  have hs := congrArg Subtype.val he
  change s(p.castSucc, p.succ) = s(q.castSucc, q.succ) at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Fin.ext
    have hv := congrArg Fin.val h.1
    simpa using hv
  · have hv₁ := congrArg Fin.val h.1
    have hv₂ := congrArg Fin.val h.2
    simp at hv₁ hv₂
    omega

theorem pathEdgeGeneral_commonColor {r n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (z : C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      (r ≤ a.val ∨ r ≤ b.val) →
      χ.get a b ((top_adj a b).2 hab) = z)
    (f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (p : Fin (r + 1))
    (houtside : r ≤ (f p.castSucc).val ∨ r ≤ (f p.succ).val) :
    (EdgeLabeling.pullback χ f.toHom) (pathEdgeGeneral r p) = z := by
  have hsource : p.castSucc ≠ p.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  have hne : f p.castSucc ≠ f p.succ := f.injective.ne hsource
  have hfresh := hχ (f p.castSucc) (f p.succ) hne houtside
  simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
    EdgeLabeling.get, pathEdgeGeneral] using hfresh

/-- If all complete-graph edges touching vertices outside the first `r` labels
have one common color, no path on `r + 2` vertices is rainbow. -/
theorem noRainbowPath_of_commonOutsideColor {r n : ℕ} {C : Type*}
    (hr : 1 ≤ r) (χ : TopEdgeLabeling (Fin n) C) (z : C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      (r ≤ a.val ∨ r ≤ b.val) →
      χ.get a b ((top_adj a b).2 hab) = z) :
    ∀ f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ := by
  intro f hf
  change Function.Injective (EdgeLabeling.pullback χ f.toHom) at hf
  obtain ⟨i, j, hij, hi, hj⟩ := two_vertices_outside_prefix f f.injective
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    two_incident_path_edges_succ (m := r + 1) (by omega) i j hij
  have hcolor (t : Fin (r + 1))
      (ht : i = t.castSucc ∨ i = t.succ ∨ j = t.castSucc ∨ j = t.succ) :
      (EdgeLabeling.pullback χ f.toHom) (pathEdgeGeneral r t) = z := by
    apply pathEdgeGeneral_commonColor χ z hχ f t
    rcases ht with ht | ht | ht | ht
    · exact Or.inl (by simpa [ht] using hi)
    · exact Or.inr (by simpa [ht] using hi)
    · exact Or.inl (by simpa [ht] using hj)
    · exact Or.inr (by simpa [ht] using hj)
  exact hpq ((pathEdgeGeneral_injective r) (hf ((hcolor p hp).trans (hcolor q hq).symm)))

end ErdosProblems.PathCliqueLower

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

/-- The complete graph on the first `r` vertices of `Fin n`. -/
def prefixCopy {r n : ℕ} (h : r ≤ n) :
    (⊤ : SimpleGraph (Fin r)).Copy (⊤ : SimpleGraph (Fin n)) :=
  (SimpleGraph.Embedding.completeGraph (Fin.castLEEmb h)).toCopy

@[simp] theorem prefixCopy_apply {r n : ℕ} (h : r ≤ n) (i : Fin r) :
    prefixCopy h i = Fin.castLE h i := rfl

/-- The canonical injection from the smaller complete graph's edge set. -/
def prefixEdgeMap {r n : ℕ} (h : r ≤ n) :
    (⊤ : SimpleGraph (Fin r)).edgeSet ↪ (⊤ : SimpleGraph (Fin n)).edgeSet :=
  (prefixCopy h).mapEdgeSet

theorem prefixEdgeMap_injective {r n : ℕ} (h : r ≤ n) :
    Function.Injective (prefixEdgeMap h) :=
  (prefixEdgeMap h).injective

/-- An edge with an endpoint outside the first `r` vertices is not mapped from the clique. -/
theorem prefix_edge_not_range {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    ¬∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy h).mapEdgeSet x =
        ⟨s(a, b), (SimpleGraph.top_adj a b).2 hab⟩ := by
  rintro ⟨x, hx⟩
  have hxval := congrArg Subtype.val hx
  change Sym2.map (Fin.castLE h) x.val = s(a, b) at hxval
  have ha : a.val < r := by
    have haMem : a ∈ Sym2.map (Fin.castLE h) x.val :=
      hxval.symm ▸ Sym2.mem_mk_left a b
    obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp haMem
    have huval : u.val < r := u.isLt
    have heq := congrArg Fin.val hu
    simpa only [Fin.val_castLE] using heq.symm ▸ huval
  have hb : b.val < r := by
    have hbMem : b ∈ Sym2.map (Fin.castLE h) x.val :=
      hxval.symm ▸ Sym2.mem_mk_right a b
    obtain ⟨u, _, hu⟩ := Sym2.mem_map.mp hbMem
    have huval : u.val < r := u.isLt
    have heq := congrArg Fin.val hu
    simpa only [Fin.val_castLE] using heq.symm ▸ huval
  omega

/-- An explicit edge between vertices `r` and `r + 1`, both outside the prefix clique. -/
def outsideEdge {r n : ℕ} (h : r + 2 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet := by
  let a : Fin n := ⟨r, by omega⟩
  let b : Fin n := ⟨r + 1, by omega⟩
  have hab : a ≠ b := by
    intro heq
    have heqval := congrArg Fin.val heq
    dsimp [a, b] at heqval
    omega
  exact ⟨s(a, b), (SimpleGraph.top_adj a b).2 hab⟩

theorem outsideEdge_not_range {r n : ℕ} (h : r + 2 ≤ n) :
    ¬∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy (by omega : r ≤ n)).mapEdgeSet x = outsideEdge h := by
  let a : Fin n := ⟨r, by omega⟩
  let b : Fin n := ⟨r + 1, by omega⟩
  have hab : a ≠ b := by
    intro heq
    have heqval := congrArg Fin.val heq
    dsimp [a, b] at heqval
    omega
  simpa only [outsideEdge] using
    (prefix_edge_not_range (by omega : r ≤ n) a b hab (Or.inl le_rfl))

end ErdosProblems.PathCliqueLower

namespace ErdosProblems.PathCliqueLower

open SimpleGraph

abbrev RawColors (r : ℕ) : Type := ((⊤ : SimpleGraph (Fin r)).edgeSet) ⊕ PUnit

noncomputable def rawCliqueColor {r n : ℕ} (h : r ≤ n) :
    TopEdgeLabeling (Fin n) (RawColors r) :=
  fun e => if he : ∃ x : (⊤ : SimpleGraph (Fin r)).edgeSet,
      (prefixCopy h).mapEdgeSet x = e then
    Sum.inl (Classical.choose he) else Sum.inr PUnit.unit

theorem rawCliqueColor_on_prefix {r n : ℕ} (h : r ≤ n)
    (x : (⊤ : SimpleGraph (Fin r)).edgeSet) :
    rawCliqueColor h ((prefixCopy h).mapEdgeSet x) = Sum.inl x := by
  classical
  unfold rawCliqueColor
  split_ifs with he
  · have hx : Classical.choose he = x :=
      (prefixCopy h).mapEdgeSet.injective (Classical.choose_spec he)
    exact congrArg Sum.inl hx
  · exact False.elim (he ⟨x, rfl⟩)

theorem rawCliqueColor_get_outside {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    (rawCliqueColor h).get a b ((top_adj a b).2 hab) = Sum.inr PUnit.unit := by
  have hnot := prefix_edge_not_range h a b hab hout
  simp [EdgeLabeling.get, rawCliqueColor, hnot]

theorem rawCliqueColor_surjective {r n : ℕ} (h : r + 2 ≤ n) :
    Function.Surjective (rawCliqueColor (by omega : r ≤ n)) := by
  intro c
  cases c with
  | inl x =>
      exact ⟨(prefixCopy (by omega : r ≤ n)).mapEdgeSet x,
        rawCliqueColor_on_prefix (by omega : r ≤ n) x⟩
  | inr u =>
      let a : Fin n := ⟨r, by omega⟩
      let b : Fin n := ⟨r + 1, by omega⟩
      have hab : a ≠ b := by
        intro he
        have hv := congrArg Fin.val he
        dsimp [a, b] at hv
        omega
      refine ⟨⟨s(a, b), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
        ((top_adj a b).2 hab)⟩, ?_⟩
      have hout : r ≤ a.val ∨ r ≤ b.val := Or.inl (by simp [a])
      simpa [EdgeLabeling.get, a, b] using
        rawCliqueColor_get_outside (by omega : r ≤ n) a b hab hout

theorem rawColors_card (r : ℕ) :
    Fintype.card (RawColors r) = r.choose 2 + 1 := by
  classical
  have hcard : Fintype.card ((⊤ : SimpleGraph (Fin r)).edgeSet) = r.choose 2 := by
    calc
      Fintype.card ((⊤ : SimpleGraph (Fin r)).edgeSet) =
          ((⊤ : SimpleGraph (Fin r)).edgeFinset).card := SimpleGraph.card_edgeSet
      _ = (Fintype.card (Fin r)).choose 2 :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
      _ = r.choose 2 := by simp
  change Fintype.card (((⊤ : SimpleGraph (Fin r)).edgeSet) ⊕ PUnit) =
    r.choose 2 + 1
  rw [Fintype.card_sum, hcard]
  simp

noncomputable def pathCliqueColor {r n : ℕ} (h : r ≤ n) :
    TopEdgeLabeling (Fin n) (Fin (r.choose 2 + 1)) :=
  fun e => Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (rawCliqueColor h e))

theorem pathCliqueColor_surjective {r n : ℕ} (h : r + 2 ≤ n) :
    Function.Surjective (pathCliqueColor (by omega : r ≤ n)) := by
  intro c
  let d : RawColors r := (Fintype.equivFin (RawColors r)).symm
    (Fin.cast (rawColors_card r).symm c)
  obtain ⟨e, he⟩ := rawCliqueColor_surjective h d
  refine ⟨e, ?_⟩
  change Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (rawCliqueColor (by omega : r ≤ n) e)) = c
  rw [he]
  simp [d]

noncomputable def freshFinColor (r : ℕ) : Fin (r.choose 2 + 1) :=
  Fin.cast (rawColors_card r)
    ((Fintype.equivFin (RawColors r)) (Sum.inr PUnit.unit))

theorem pathCliqueColor_get_outside {r n : ℕ} (h : r ≤ n)
    (a b : Fin n) (hab : a ≠ b) (hout : r ≤ a.val ∨ r ≤ b.val) :
    (pathCliqueColor h).get a b ((top_adj a b).2 hab) = freshFinColor r := by
  have hfresh := rawCliqueColor_get_outside h a b hab hout
  simpa [pathCliqueColor, freshFinColor, EdgeLabeling.get] using
    congrArg (fun c : RawColors r =>
      Fin.cast (rawColors_card r) ((Fintype.equivFin (RawColors r)) c)) hfresh

def admissiblePathCounts (r n : ℕ) : Set ℕ :=
  {m | ∃ χ : TopEdgeLabeling (Fin n) (Fin m), Function.Surjective χ ∧
    ∀ f : (pathGraph (r + 2)).Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ}

theorem admissiblePathCounts_bddAbove (r n : ℕ) :
    BddAbove (admissiblePathCounts r n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro m hm
  obtain ⟨χ, hχ, _⟩ := hm
  simpa using Fintype.card_le_of_surjective χ hχ

/-- The clique construction gives the first term of the path lower bound
for every `r ≥ 3` and `n ≥ r + 2`. -/
theorem pathCliqueLower_r {r n : ℕ} (hr : 3 ≤ r) (h : r + 2 ≤ n) :
    r.choose 2 + 1 ≤ antiRamseyNum (pathGraph (r + 2)) n := by
  change r.choose 2 + 1 ≤ sSup (admissiblePathCounts r n)
  apply le_csSup (admissiblePathCounts_bddAbove r n)
  refine ⟨pathCliqueColor (by omega : r ≤ n), pathCliqueColor_surjective h, ?_⟩
  exact noRainbowPath_of_commonOutsideColor (by omega : 1 ≤ r)
    (pathCliqueColor (by omega : r ≤ n)) (freshFinColor r)
    (pathCliqueColor_get_outside (by omega : r ≤ n))

/-- The first term of the proposed exact `P_k` formula is a uniform lower bound
in the original quantified range `n ≥ k ≥ 5`. -/
theorem pathCliqueLower {k n : ℕ} (hk : 5 ≤ k) (hkn : k ≤ n) :
    (k - 2).choose 2 + 1 ≤ antiRamseyNum (pathGraph k) n := by
  let r := k - 2
  have hr : 3 ≤ r := by dsimp [r]; omega
  have h : r + 2 ≤ n := by dsimp [r]; omega
  have heq : r + 2 = k := by dsimp [r]; omega
  have hres := pathCliqueLower_r hr h
  dsimp [r] at hres
  rw [show k - 2 + 2 = k by omega] at hres
  exact hres

end ErdosProblems.PathCliqueLower

namespace ErdosProblems.PathCliqueEGDensity

/-- A clique cap and the Erdős–Gallai edge inequality give the exact density
needed for each whole positive tail piece, including the `d=2,v=1` boundary. -/
theorem clique_eg_density (d v e : ℕ) (hd : 2 ≤ d) (hv : 1 ≤ v)
    (hclique : e ≤ v.choose 2) (hEG : 2 * e ≤ (d - 1) * v) :
    2 * d * (e + 1) ≤ (d * (d - 1) + 2) * v := by
  have hdsub : (d - 1) + 1 = d := by omega
  have hdsubR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast hdsub
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hclR : (e : ℝ) ≤ (v.choose 2 : ℝ) := by exact_mod_cast hclique
  rw [Nat.cast_choose_two ℝ v] at hclR
  have hEGR : 2 * (e : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (v : ℝ) := by
    exact_mod_cast hEG
  rw [hsub] at hEGR
  have hreal :
      2 * (d : ℝ) * ((e : ℝ) + 1) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + 2) * (v : ℝ) := by
    by_cases hvd : v ≤ d
    · have hvdR : (v : ℝ) ≤ (d : ℝ) := by exact_mod_cast hvd
      have hDV : (2 : ℝ) ≤ (d : ℝ) * (v : ℝ) := by
        have hprod := mul_nonneg
          (sub_nonneg.mpr hdR) (sub_nonneg.mpr hvR)
        nlinarith only [hdR, hvR, hprod]
      have hdeficit :
          0 ≤ ((d : ℝ) - (v : ℝ)) * ((d : ℝ) * (v : ℝ) - 2) :=
        mul_nonneg (sub_nonneg.mpr hvdR) (sub_nonneg.mpr hDV)
      have hweighted := mul_le_mul_of_nonneg_left hclR
        (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
      nlinarith only [hweighted, hdeficit]
    · have hlarge : d ≤ v := by omega
      have hlargeR : (d : ℝ) ≤ (v : ℝ) := by exact_mod_cast hlarge
      have hweighted := mul_le_mul_of_nonneg_left hEGR (Nat.cast_nonneg d)
      nlinarith only [hweighted, hlargeR]
  have hcast :
      ((2 * d * (e + 1) : ℕ) : ℝ) ≤
        (((d * (d - 1) + 2) * v : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, hsub] using hreal
  exact_mod_cast hcast

end ErdosProblems.PathCliqueEGDensity

namespace ErdosProblems.PathCliqueTwoLeaves

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Move the larger endpoint of a natural-order edge to a far nonzero vertex.
The swap fixes every vertex at position zero and destroys that adjacency. -/
theorem swap_breaks_ordered_edge {m : ℕ} (hm : 5 ≤ m)
    (a b : Fin m) (hab : a.val + 1 = b.val) :
    ∃ π : Equiv.Perm (Fin m),
      (∀ z : Fin m, z.val = 0 → π z = z) ∧
      (∀ i : Fin m, π (π i) = i) ∧
      ¬ (pathGraph m).Adj (π a) (π b) := by
  let c : Fin m :=
    ⟨if a.val = 0 then 3 else if a.val ≤ 2 then 4 else 1,
      by split_ifs <;> omega⟩
  have hc0 : c.val ≠ 0 := by
    change (if a.val = 0 then 3 else if a.val ≤ 2 then 4 else 1) ≠ (0 : ℕ)
    split_ifs <;> decide
  have habne : a ≠ b := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  have hac : a ≠ c := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [c] at hv
    split_ifs at hv <;> omega
  let π : Equiv.Perm (Fin m) := Equiv.swap b c
  refine ⟨π, ?_, ?_, ?_⟩
  · intro z hz
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      exact hc0 (hv.symm.trans hz)
  · intro i
    exact Equiv.swap_apply_self b c i
  · change ¬ (pathGraph m).Adj (Equiv.swap b c a) (Equiv.swap b c b)
    rw [Equiv.swap_apply_of_ne_of_ne habne hac, Equiv.swap_apply_left,
      pathGraph_adj]
    dsimp [c]
    split_ifs <;> omega

theorem avoid_ordered_owner {V : Type*} {m : ℕ}
    (hm : 5 ≤ m) (core : Fin m → V) (hcore : Function.Injective core)
    (z : Fin m) (hz : z.val = 0) (old : Sym2 V)
    (a b : Fin m) (hab : a.val + 1 = b.val)
    (howner : old = s(core a, core b)) :
    ∃ π : Equiv.Perm (Fin m), π z = z ∧
      ∀ i j : Fin m, (pathGraph m).Adj i j →
        old ≠ s(core (π i), core (π j)) := by
  obtain ⟨π, hzero, hinv, hnon⟩ := swap_breaks_ordered_edge hm a b hab
  refine ⟨π, hzero z hz, ?_⟩
  intro i j hij heq
  have hpairs : s(π i, π j) = s(a, b) := by
    apply Sym2.map.injective hcore
    simpa only [Sym2.map_mk] using heq.symm.trans howner
  rcases Sym2.eq_iff.mp hpairs with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have hi' : i = π a := by
      simpa only [hinv] using congrArg π hi
    have hj' : j = π b := by
      simpa only [hinv] using congrArg π hj
    exact hnon (by simpa only [hi', hj'] using hij)
  · have hi' : i = π b := by
      simpa only [hinv] using congrArg π hi
    have hj' : j = π a := by
      simpa only [hinv] using congrArg π hj
    exact hnon (by simpa only [hi', hj'] using hij.symm)

/-- The actual owner is arbitrary. If absent from the natural core path,
use that path; otherwise the explicit far-vertex swap avoids it. -/
theorem core_order_avoids_one {V : Type*} {m : ℕ}
    (hm : 5 ≤ m) (core : Fin m → V) (hcore : Function.Injective core)
    (z : Fin m) (hz : z.val = 0) (old : Sym2 V) :
    ∃ π : Equiv.Perm (Fin m), π z = z ∧
      ∀ i j : Fin m, (pathGraph m).Adj i j →
        old ≠ s(core (π i), core (π j)) := by
  classical
  by_cases hex : ∃ a b : Fin m,
      (pathGraph m).Adj a b ∧ old = s(core a, core b)
  · obtain ⟨a, b, hab, howner⟩ := hex
    rcases pathGraph_adj.mp hab with hab | hba
    · exact avoid_ordered_owner hm core hcore z hz old a b hab howner
    · apply avoid_ordered_owner hm core hcore z hz old b a hba
      exact howner.trans Sym2.eq_swap
  · refine ⟨Equiv.refl _, rfl, ?_⟩
    intro i j hij heq
    exact hex ⟨i, j, hij, heq⟩

theorem two_prefix_injective {V : Type*} {m : ℕ}
    (p : Fin m → V) (hp : Function.Injective p) (c d : V)
    (hcd : c ≠ d) (hc : ∀ i, c ≠ p i) (hd : ∀ i, d ≠ p i) :
    Function.Injective (Fin.cons c (Fin.cons d p)) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact hcd (by simpa using hi.symm)
    | succ i => exact hc i (by simpa using hi.symm)
  · apply Fin.cons_injective_of_injective
    · rintro ⟨i, hi⟩
      exact hd i hi.symm
    · exact hp

/-- The literal Copy adapter uses actual pathGraph adjacency and two cons
steps. Its adjacency premises are derived inside the coloring caller. -/
def prefix_two_copy {V : Type*} {m : ℕ}
    (G : SimpleGraph V) (p : Fin m → V) (c d : V)
    (hw : Function.Injective (Fin.cons c (Fin.cons d p)))
    (z : Fin m) (hz : z.val = 0)
    (hcd : G.Adj c d) (hdz : G.Adj d (p z))
    (hsteps : ∀ i j : Fin m, (pathGraph m).Adj i j → G.Adj (p i) (p j)) :
    (pathGraph (m + 2)).Copy G := by
  let w : Fin (m + 2) → V := Fin.cons c (Fin.cons d p)
  have hnext (i j : Fin (m + 2)) (hij : i.val + 1 = j.val) :
      G.Adj (w i) (w j) := by
    cases i using Fin.cases with
    | zero =>
      have hj : j = (0 : Fin (m + 1)).succ := by
        apply Fin.ext
        simpa using hij.symm
      rw [hj]
      simpa [w] using hcd
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        have hj : j = z.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_zero] at hij ⊢
          omega
        rw [hj]
        simpa [w] using hdz
      | succ i =>
        have hjbound := j.isLt
        let j' : Fin m := ⟨j.val - 2, by
          simp only [Fin.val_succ] at hij
          omega⟩
        have hj : j = j'.succ.succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          dsimp [j']
          simp only [Fin.val_succ] at hij
          omega
        have hbase : (pathGraph m).Adj i j' := by
          apply pathGraph_adj.mpr
          left
          dsimp [j']
          simp only [Fin.val_succ] at hij
          omega
        rw [hj]
        simpa [w] using hsteps i j' hbase
  let φ : (pathGraph (m + 2)) →g G :=
    ⟨w, by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · exact hnext i j hij
      · exact (hnext j i hji).symm⟩
  exact ⟨φ, hw⟩

/-- A selected clique of order m≥5 and two distinct extra vertices with
selected spokes to the same core hub force an original rainbow P_(m+2).
No owner, rainbow path, inducedness or full-graph S1 premise is supplied. -/
theorem rainbow_path_of_representative_clique_and_two_leaves {n q m : ℕ}
    (hm : 5 ≤ m) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (core : Fin m → Fin n) (a b : Fin n)
    (hu : Function.Injective (Fin.cons a (Fin.cons b core)))
    (hK : ∀ i j : Fin m, i ≠ j →
      (selectedGraph χ r).Adj (core i) (core j))
    (ha : (selectedGraph χ r).Adj a (core ⟨0, by omega⟩))
    (hb : (selectedGraph χ r).Adj b (core ⟨0, by omega⟩)) :
    ∃ f : (pathGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  classical
  let z : Fin m := ⟨0, by omega⟩
  have hz : z.val = 0 := rfl
  change (selectedGraph χ r).Adj a (core z) at ha
  change (selectedGraph χ r).Adj b (core z) at hb
  have haRange : a ∉ Set.range (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).1
  have htail : Function.Injective (Fin.cons b core) :=
    (Fin.cons_injective_iff.mp hu).2
  have hbRange : b ∉ Set.range core := (Fin.cons_injective_iff.mp htail).1
  have hcore : Function.Injective core := (Fin.cons_injective_iff.mp htail).2
  have hab : a ≠ b := by
    intro heq
    apply haRange
    exact ⟨0, by simpa using heq.symm⟩
  have hacore (i : Fin m) : a ≠ core i := by
    intro heq
    apply haRange
    exact ⟨i.succ, by simpa using heq.symm⟩
  have hbcore (i : Fin m) : b ≠ core i := by
    intro heq
    exact hbRange ⟨i, heq.symm⟩
  let e : HostEdge n :=
    ⟨s(a, b), (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
      ((top_adj _ _).mpr hab)⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretain {x y : Fin n} (hadj : L.Adj x y) (hne : old ≠ s(x, y)) :
      L'.Adj x y := by
    have he : s(x, y) ∈ L.edgeSet := hadj
    have hed : s(x, y) ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact SimpleGraph.edgeSet_mono hle hed
  have hchord : L'.Adj a b := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  obtain ⟨π, hfix, havoid⟩ := core_order_avoids_one hm core hcore z hz old
  let p : Fin m → Fin n := core ∘ π
  have hp : Function.Injective p := hcore.comp π.injective
  have hpz : p z = core z := by simp only [p, Function.comp_apply, hfix]
  have hsteps (i j : Fin m) (hij : (pathGraph m).Adj i j) :
      L'.Adj (p i) (p j) := by
    have hne : i ≠ j := hij.ne
    exact hretain (hK (π i) (π j) (π.injective.ne hne)) (havoid i j hij)
  have haP (i : Fin m) : a ≠ p i := hacore (π i)
  have hbP (i : Fin m) : b ≠ p i := hbcore (π i)
  by_cases holdb : old = s(b, core z)
  · have holda : old ≠ s(a, core z) := by
      intro heq
      have hedge : s(b, core z) = s(a, core z) := holdb.symm.trans heq
      rcases Sym2.eq_iff.mp hedge with ⟨hba, _⟩ | ⟨_, hza⟩
      · exact hab hba.symm
      · exact hacore z hza.symm
    have hspoke : L'.Adj a (p z) := by
      rw [hpz]
      exact hretain ha holda
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p b a
        (two_prefix_injective p hp b a hab.symm hbP haP)
        z hz hchord.symm hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f
  · have hspoke : L'.Adj b (p z) := by
      rw [hpz]
      exact hretain hb holdb
    let f : (pathGraph (m + 2)).Copy L' :=
      prefix_two_copy L' p a b
        (two_prefix_injective p hp a b hab haP hbP)
        z hz hchord hspoke hsteps
    refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
    simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

end ErdosProblems.PathCliqueTwoLeaves

namespace ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ambient image of an actual component of the actual vertex deletion. -/
def deletedComponentVertices (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) : Set V :=
  Subtype.val '' D.supp

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_ne (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) {v : V}
    (hv : v ∈ deletedComponentVertices G c D) : v ≠ c := by
  rcases hv with ⟨u, _, rfl⟩
  exact u.property

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_adj_closed (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) {u v : V}
    (hu : u ∈ deletedComponentVertices G c D) (huv : G.Adj u v)
    (hv : v ≠ c) : v ∈ deletedComponentVertices G c D := by
  rcases hu with ⟨u', hu', rfl⟩
  refine ⟨⟨v, hv⟩, ?_, rfl⟩
  exact D.mem_supp_of_adj_mem_supp hu' huv

omit [Fintype V] [DecidableEq V] in
theorem deletedComponentVertices_disjoint (G : SimpleGraph V) (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hDE : D ≠ E) :
    Disjoint (deletedComponentVertices G c D) (deletedComponentVertices G c E) := by
  apply Set.disjoint_left.mpr
  intro v hvD hvE
  rcases hvD with ⟨d, hd, rfl⟩
  rcases hvE with ⟨e, he, hval⟩
  have hde : d = e := Subtype.ext hval.symm
  have hd' := (D.mem_supp_iff d).mp hd
  have he' := (E.mem_supp_iff e).mp he
  exact hDE (hd'.symm.trans (hde.symm ▸ he'))

omit [DecidableEq V] in
theorem exists_root_neighbor_in_deleted_component (G : SimpleGraph V) (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hconn : G.Connected) :
    ∃ a ∈ deletedComponentVertices G c D, G.Adj c a := by
  classical
  by_contra hnone
  push Not at hnone
  obtain ⟨d, hd⟩ := D.nonempty_supp
  have hstart : d.val ∈ deletedComponentVertices G c D := ⟨d, hd, rfl⟩
  have hclosed : ∀ {u v : V}, u ∈ deletedComponentVertices G c D →
      G.Adj u v → v ∈ deletedComponentVertices G c D := by
    intro u v hu huv
    have hv : v ≠ c := by
      intro heq
      exact hnone u hu (heq ▸ huv.symm)
    exact deletedComponentVertices_adj_closed G c D hu huv hv
  have hwalk : ∀ {u v : V}, (p : G.Walk u v) →
      u ∈ deletedComponentVertices G c D → v ∈ deletedComponentVertices G c D := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v huw p ih => exact fun hu => ih (hclosed hu huw)
  obtain ⟨p⟩ := hconn.preconnected d.val c
  exact deletedComponentVertices_ne G c D (hwalk p hstart) rfl

theorem exists_neighbor_outside_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v : V, 3 ≤ G.degree v) (v x y : V) :
    ∃ w, G.Adj v w ∧ w ≠ x ∧ w ≠ y := by
  classical
  have hnot : ¬ G.neighborFinset v ⊆ ({x, y} : Finset V) := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have htwo : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
    have hthree := hmin v
    change 3 ≤ (G.neighborFinset v).card at hthree
    omega
  obtain ⟨w, hw, hout⟩ := Finset.not_subset.mp hnot
  refine ⟨w, (G.mem_neighborFinset v w).mp hw, ?_, ?_⟩ <;>
    intro heq <;> subst w <;> simp at hout

theorem exists_rooted_four_in_deleted_component (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V)
    (D : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v) :
    ∃ a b d : V, a ∈ deletedComponentVertices G c D ∧
      b ∈ deletedComponentVertices G c D ∧ d ∈ deletedComponentVertices G c D ∧
      [c, a, b, d].Nodup ∧ G.Adj c a ∧ G.Adj a b ∧ G.Adj b d := by
  classical
  obtain ⟨a, ha, hca⟩ := exists_root_neighbor_in_deleted_component G c D hconn
  obtain ⟨b, hab, hbc, hba⟩ := exists_neighbor_outside_pair G hmin a c a
  have hb := deletedComponentVertices_adj_closed G c D ha hab hbc
  obtain ⟨d, hbd, hdc, hda⟩ := exists_neighbor_outside_pair G hmin b c a
  have hd := deletedComponentVertices_adj_closed G c D hb hbd hdc
  have hac := deletedComponentVertices_ne G c D ha
  have hdb : d ≠ b := hbd.ne.symm
  refine ⟨a, b, d, ha, hb, hd, ?_, hca, hab, hbd⟩
  simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
    not_or, and_true]
  grind

/-- Literal joined rooted P5 and P4 contradict P8-freeness on the SAME graph. -/
theorem no_rooted_five_in_deleted_component (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (hDE : D ≠ E)
    (a b d w : V)
    (ha : a ∈ deletedComponentVertices G c D)
    (hb : b ∈ deletedComponentVertices G c D)
    (hd : d ∈ deletedComponentVertices G c D)
    (hw : w ∈ deletedComponentVertices G c D)
    (hnodup : [c, a, b, d, w].Nodup)
    (hca : G.Adj c a) (hab : G.Adj a b) (hbd : G.Adj b d)
    (hdw : G.Adj d w) : False := by
  classical
  obtain ⟨p, q, s, hp, hq, hs, hE, hcp, hpq, hqs⟩ :=
    exists_rooted_four_in_deleted_component G c E hconn hmin
  have hdis := Set.disjoint_left.mp (deletedComponentVertices_disjoint G c D E hDE)
  have hcross : ∀ x ∈ ({a, b, d, w} : Finset V),
      ∀ y ∈ ({p, q, s} : Finset V), x ≠ y := by
    intro x hx y hy hxy
    have hxD : x ∈ deletedComponentVertices G c D := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hyE : y ∈ deletedComponentVertices G c E := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    exact hdis hxD (hxy.symm ▸ hyE)
  let joined : G.Walk w s :=
    Walk.cons hdw.symm (Walk.cons hbd.symm (Walk.cons hab.symm
      (Walk.cons hca.symm (Walk.cons hcp (Walk.cons hpq (Walk.cons hqs Walk.nil))))))
  have hpath : joined.IsPath := by
    apply Walk.IsPath.mk'
    change [w, d, b, a, c, p, q, s].Nodup
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_or, and_true] at hnodup hE ⊢
    have hap := hcross a (by simp) p (by simp)
    have haq := hcross a (by simp) q (by simp)
    have has := hcross a (by simp) s (by simp)
    have hbp := hcross b (by simp) p (by simp)
    have hbq := hcross b (by simp) q (by simp)
    have hbs := hcross b (by simp) s (by simp)
    have hdp := hcross d (by simp) p (by simp)
    have hdq := hcross d (by simp) q (by simp)
    have hds := hcross d (by simp) s (by simp)
    have hwp := hcross w (by simp) p (by simp)
    have hwq := hcross w (by simp) q (by simp)
    have hws := hcross w (by simp) s (by simp)
    grind
  apply hfree
  exact ⟨by simpa only [joined, Walk.length_cons, Walk.length_nil] using hpath.pathGraphCopy⟩

/-- Every actual deletion component is a triangle when a second component exists.
The conclusion counts the explicit deleted-support carrier, without a carrier
identification or a supplied favorable rooted path. -/
theorem deleted_component_card_eq_three_of_distinct_component
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hmin : ∀ v : V, 3 ≤ G.degree v) (hfree : (pathGraph 8).Free G)
    (c : V) (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent)
    (hDE : D ≠ E) :
    Nat.card {v : {x : V // x ≠ c} // v ∈ D.supp} = 3 := by
  classical
  obtain ⟨a, b, d, ha, hb, hd, hfour, hca, hab, hbd⟩ :=
    exists_rooted_four_in_deleted_component G c D hconn hmin
  have hac := deletedComponentVertices_ne G c D ha
  have hbc := deletedComponentVertices_ne G c D hb
  have hdc := deletedComponentVertices_ne G c D hd
  have habne : a ≠ b := hab.ne
  have hadne : a ≠ d := by
    have hh := hfour
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
      not_or, and_true] at hh
    grind
  have hbdne : b ≠ d := hbd.ne
  have hterminal : ∀ w : V, G.Adj d w → w = c ∨ w = a ∨ w = b := by
    intro w hdw
    by_contra hout
    have hwc : w ≠ c := by grind
    have hwa : w ≠ a := by grind
    have hwb : w ≠ b := by grind
    have hwd : w ≠ d := hdw.ne.symm
    have hw := deletedComponentVertices_adj_closed G c D hd hdw hwc
    have hfive : [c, a, b, d, w].Nodup := by
      have hh := hfour
      simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
        not_or, and_true] at hh ⊢
      grind
    exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
      a b d w ha hb hd hw hfive hca hab hbd hdw
  have hNsub : G.neighborFinset d ⊆ ({c, a, b} : Finset V) := by
    intro w hw
    have hcases := hterminal w ((G.mem_neighborFinset d w).mp hw)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hcases
  have hNcard : ({c, a, b} : Finset V).card ≤ (G.neighborFinset d).card := by
    have hsmall : ({c, a, b} : Finset V).card ≤ 3 := Finset.card_le_three
    exact hsmall.trans (hmin d)
  have hNeq := Finset.eq_of_subset_of_card_le hNsub hNcard
  have hdcAdj : G.Adj d c := (G.mem_neighborFinset d c).mp (by rw [hNeq]; simp)
  have hdaAdj : G.Adj d a := (G.mem_neighborFinset d a).mp (by rw [hNeq]; simp)
  let T : Set V := {a, b, d}
  have hTsub : T ⊆ deletedComponentVertices G c D := by
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hclosedT : ∀ {u v : V}, u ∈ T →
      v ∈ deletedComponentVertices G c D → G.Adj u v → v ∈ T := by
    intro u v hu hv huv
    by_contra hvout
    have hvc := deletedComponentVertices_ne G c D hv
    have hvne : v ≠ a ∧ v ≠ b ∧ v ≠ d := by simpa [T] using hvout
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hua | hub | hud
    · subst u
      have hfive : [c, d, b, a, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        d b a v hd hb ha hv hfive hdcAdj.symm hbd.symm hab.symm huv
    · subst u
      have hfive : [c, a, d, b, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        a d b v ha hd hb hv hfive hca hdaAdj.symm hbd.symm huv
    · subst u
      have hfive : [c, a, b, d, v].Nodup := by
        simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil,
          not_or, and_true]
        grind
      exact no_rooted_five_in_deleted_component G c D E hconn hmin hfree hDE
        a b d v ha hb hd hv hfive hca hab hbd huv
  have hwalkT : ∀ {u v : {x : V // x ≠ c}},
      (p : (G.induce {x : V | x ≠ c}).Walk u v) → u.val ∈ T → v.val ∈ T := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v huw p ih =>
      intro hu
      have hwD := deletedComponentVertices_adj_closed G c D (hTsub hu) huw w.property
      exact ih (hclosedT hu hwD huw)
  have hS : deletedComponentVertices G c D = T := by
    apply Set.Subset.antisymm
    · intro v hv
      rcases ha with ⟨a', ha', haval⟩
      rcases hv with ⟨v', hv', hvval⟩
      obtain ⟨p⟩ := D.reachable_of_mem_supp ha' hv'
      have haT : a'.val ∈ T := by rw [haval]; simp [T]
      have hvT := hwalkT p haT
      simpa only [hvval] using hvT
    · exact hTsub
  let project : {v : {x : V // x ≠ c} // v ∈ D.supp} →
      deletedComponentVertices G c D :=
    fun v => ⟨v.val.val, ⟨v.val, v.property, rfl⟩⟩
  have hproject : Function.Bijective project := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg (fun z : deletedComponentVertices G c D => z.val) huv
      change u.val.val = v.val.val at hval
      exact hval
    · intro v
      rcases v.property with ⟨u, hu, huv⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      exact huv
  have hcardS : Nat.card (deletedComponentVertices G c D) = 3 := by
    rw [Nat.card_eq_card_toFinset]
    have hfin : (deletedComponentVertices G c D).toFinset = ({a, b, d} : Finset V) := by
      ext v
      simp [hS, T]
    rw [hfin]
    simp [habne, hadne, hbdne]
  exact (Nat.card_congr (Equiv.ofBijective project hproject)).trans hcardS

end ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105

namespace ErdosProblems.PathUpperReduction.PathEightWindmillCount1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.PathEightDeletedComponentThree1105
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nonroot_degree_three_and_root_adj
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (c : V)
    (D0 E0 : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hD0E0 : D0 ≠ E0)
    (v : V) (hv : v ≠ c) : G.degree v = 3 ∧ G.Adj c v := by
  classical
  let x : {w : V // w ≠ c} := ⟨v, hv⟩
  let D := (G.induce {w : V | w ≠ c}).connectedComponentMk x
  obtain ⟨E, hDE⟩ : ∃ E : (G.induce {w : V | w ≠ c}).ConnectedComponent, D ≠ E := by
    by_cases hDD0 : D = D0
    · exact ⟨E0, fun hDE => hD0E0 (hDD0.symm.trans hDE)⟩
    · exact ⟨D0, hDD0⟩
  have hDcard := deleted_component_card_eq_three_of_distinct_component
    G hconn hmin hfree c D E hDE
  let S : Finset V := D.supp.toFinset.image (fun u : {w : V // w ≠ c} => u.val)
  have hScard : S.card = 3 := by
    calc
      S.card = D.supp.toFinset.card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      _ = Nat.card {u : {w : V // w ≠ c} // u ∈ D.supp} :=
        (Nat.card_eq_card_toFinset D.supp).symm
      _ = 3 := hDcard
  have hSmem : ∀ w : V, w ∈ S ↔ w ∈ deletedComponentVertices G c D := by
    intro w
    simp [S, deletedComponentVertices]
  have hvD : v ∈ deletedComponentVertices G c D := by
    refine ⟨x, ?_, rfl⟩
    change (G.induce {w : V | w ≠ c}).connectedComponentMk x = D
    rfl
  have hvS : v ∈ S := (hSmem v).mpr hvD
  have hcS : c ∉ S := by
    intro hc
    exact deletedComponentVertices_ne G c D ((hSmem c).mp hc) rfl
  have hcErase : c ∉ S.erase v := by
    intro hc
    exact hcS (Finset.mem_erase.mp hc).2
  have hEraseCard : (S.erase v).card + 1 = 3 := by
    simpa only [hScard] using Finset.card_erase_add_one hvS
  let T : Finset V := insert c (S.erase v)
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hcErase]
    exact hEraseCard
  have hNsub : G.neighborFinset v ⊆ T := by
    intro w hw
    have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    by_cases hwc : w = c
    · subst w
      simp [T]
    · have hwD := deletedComponentVertices_adj_closed G c D hvD hvw hwc
      have hwS : w ∈ S := (hSmem w).mpr hwD
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw.ne.symm, hwS⟩)
  have hNmin : 3 ≤ (G.neighborFinset v).card := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hmin v
  have hNback : T.card ≤ (G.neighborFinset v).card := by
    rw [hTcard]
    exact hNmin
  have hNeq := Finset.eq_of_subset_of_card_le hNsub hNback
  have hdegree : G.degree v = 3 := by
    rw [← G.card_neighborFinset_eq_degree v, hNeq]
    exact hTcard
  have hvc : G.Adj v c := (G.mem_neighborFinset v c).mp (by rw [hNeq]; simp [T])
  exact ⟨hdegree, hvc.symm⟩

/-- The actual edge count in the vertex-cut branch. -/
theorem windmill_edge_count_of_distinct_deleted_components
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hfree : (pathGraph 8).Free G) (c : V)
    (D E : (G.induce {v : V | v ≠ c}).ConnectedComponent) (hDE : D ≠ E) :
    G.edgeFinset.card = 2 * Fintype.card V - 2 := by
  classical
  have hnonroot : ∀ v : V, v ≠ c → G.degree v = 3 ∧ G.Adj c v := by
    intro v hv
    exact nonroot_degree_three_and_root_adj G hconn hmin hfree c D E hDE v hv
  have huniversal : G.IsUniversal c := by
    intro v hcv
    exact (hnonroot v hcv.symm).2
  have hcDegree : G.degree c = Fintype.card V - 1 :=
    (G.degree_eq_card_sub_one c).mpr huniversal
  let rest : Finset V := Finset.univ.erase c
  have hRestCard : rest.card + 1 = Fintype.card V := by
    simpa only [rest, Finset.card_univ] using
      Finset.card_erase_add_one (s := (Finset.univ : Finset V)) (a := c) (by simp)
  have hRestSum : (∑ v ∈ rest, G.degree v) = rest.card * 3 := by
    apply Finset.sum_const_nat
    intro v hv
    exact (hnonroot v (Finset.mem_erase.mp hv).1).1
  have hSplit : G.degree c + (∑ v ∈ rest, G.degree v) = 2 * G.edgeFinset.card := by
    calc
      G.degree c + (∑ v ∈ rest, G.degree v) = ∑ v : V, G.degree v := by
        simpa only [rest] using
          Finset.add_sum_erase (Finset.univ : Finset V) (fun v => G.degree v)
            (by simp : c ∈ (Finset.univ : Finset V))
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  omega

end ErdosProblems.PathUpperReduction.PathEightWindmillCount1105

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- Yuan's star construction at `k = 5`, with `n` colors on `K_n`. -/
def starColor (n : ℕ) [NeZero n] : TopEdgeLabeling (Fin n) (Fin n) :=
  EdgeLabeling.mk
    (fun a b _ => if a = 0 ∨ b = 0 then max a b else 0)
    (by intro a b _; simp [or_comm, max_comm])

@[simp] theorem starColor_get {n : ℕ} [NeZero n] (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b) :
    (starColor n).get a b hab = if a = 0 ∨ b = 0 then max a b else 0 := by
  rfl

/-- An edge away from the distinguished vertex has color zero. -/
theorem starColor_get_nonincident {n : ℕ} [NeZero n] (a b : Fin n)
    (hab : (⊤ : SimpleGraph (Fin n)).Adj a b)
    (ha : a ≠ 0) (hb : b ≠ 0) : (starColor n).get a b hab = 0 := by
  simp [starColor_get, ha, hb]

/-- Every label appears: nonzero label `i` occurs on `{0,i}`, and label zero
occurs on `{1,2}`. -/
theorem starColor_surjective (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    Function.Surjective (starColor n) := by
  intro i
  by_cases hi : i = (0 : Fin n)
  · subst i
    let a : Fin n := ⟨1, by omega⟩
    let b : Fin n := ⟨2, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a, b] at hv
    have ha : a ≠ (0 : Fin n) := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a] at hv
    have hb : b ≠ (0 : Fin n) := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [b] at hv
    refine ⟨⟨s(a, b), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
      ((top_adj a b).2 hab)⟩, ?_⟩
    exact starColor_get_nonincident a b ((top_adj a b).2 hab) ha hb
  · refine ⟨⟨s((0 : Fin n), i), ((⊤ : SimpleGraph (Fin n)).mem_edgeSet).2
      ((top_adj 0 i).2 (Ne.symm hi))⟩, ?_⟩
    change (starColor n).get 0 i ((top_adj 0 i).2 (Ne.symm hi)) = i
    rw [starColor_get]
    simp

end ErdosProblems.AntiRamseyPathFive

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- The component supports partition a finite vertex carrier. -/
theorem vertex_card_eq_sum_component_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V = ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
  classical
  let supportFinset : G.ConnectedComponent → Finset V := fun C => C.supp.toFinset
  have hpair : Set.PairwiseDisjoint
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent)
      supportFinset := by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr
      (G.pairwise_disjoint_supp_connectedComponent hCD)
  have hcover : (Finset.univ : Finset G.ConnectedComponent).biUnion supportFinset =
      (Finset.univ : Finset V) := by
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      exact Finset.mem_biUnion.mpr
        ⟨G.connectedComponentMk v, Finset.mem_univ _, by simp [supportFinset]⟩
  calc
    Fintype.card V = (Finset.univ : Finset V).card := by simp
    _ = ((Finset.univ : Finset G.ConnectedComponent).biUnion supportFinset).card :=
      congrArg Finset.card hcover.symm
    _ = ∑ C : G.ConnectedComponent, (supportFinset C).card := by
      simpa using Finset.card_biUnion hpair
    _ = ∑ C : G.ConnectedComponent, Fintype.card C.supp := by
      simp [supportFinset, Set.toFinset_card]

/-- The induced component edges partition a finite simple graph's edges. -/
theorem edge_card_eq_sum_component_edge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card = ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
  classical
  let componentEdges : G.ConnectedComponent → Finset (Sym2 V) := fun C =>
    G.edgeFinset.filter fun e => e.toFinset ⊆ C.supp.toFinset
  have hpair : Set.PairwiseDisjoint
      ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent)
      componentEdges := by
    intro C _ D _ hCD
    apply Finset.disjoint_left.mpr
    intro e heC heD
    have hefirst : e.out.1 ∈ e.toFinset :=
      Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)
    have hC : e.out.1 ∈ C.supp := by
      have h := (Finset.mem_filter.mp heC).2 hefirst
      simpa using h
    have hD : e.out.1 ∈ D.supp := by
      have h := (Finset.mem_filter.mp heD).2 hefirst
      simpa using h
    have hEq : C = D := by
      have h₁ := (C.mem_supp_iff e.out.1).mp hC
      have h₂ := (D.mem_supp_iff e.out.1).mp hD
      exact h₁.symm.trans h₂
    exact hCD hEq
  have hcover : (Finset.univ : Finset G.ConnectedComponent).biUnion componentEdges =
      G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp heC).1
    · intro heG
      induction e using Sym2.inductionOn with
      | hf u w =>
        let C : G.ConnectedComponent := G.connectedComponentMk u
        have hu : u ∈ C.supp := by simp [C]
        have hadj : G.Adj u w := by
          simpa only [G.mem_edgeFinset, G.mem_edgeSet] using heG
        have hw : w ∈ C.supp := (C.mem_supp_congr_adj hadj).mp hu
        refine Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, ?_⟩
        refine Finset.mem_filter.mpr ⟨heG, ?_⟩
        intro v hv
        have hvuw : v = u ∨ v = w := by
          simpa [Sym2.toFinset_mk_eq] using hv
        rcases hvuw with rfl | rfl
        · simpa using hu
        · simpa using hw
  calc
    G.edgeFinset.card =
        ((Finset.univ : Finset G.ConnectedComponent).biUnion componentEdges).card :=
      congrArg Finset.card hcover.symm
    _ = ∑ C : G.ConnectedComponent, (componentEdges C).card := by
      simpa using Finset.card_biUnion hpair
    _ = ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
      apply Finset.sum_congr rfl
      intro C _
      have hset : (↑C.supp.toFinset : Set V) = C.supp := by
        ext v
        simp
      have hcard : (G.induce (↑C.supp.toFinset : Set V)).edgeFinset.card =
          Nat.card (G.induce (↑C.supp.toFinset : Set V)).edgeSet := by
        rw [Nat.card_eq_fintype_card]
        exact (G.induce (↑C.supp.toFinset : Set V)).card_edgeSet.symm
      have h := (G.card_filter_edgeFinset_toFinset_subset C.supp.toFinset).trans hcard
      rw [hset] at h
      change (componentEdges C).card = Nat.card (G.induce C.supp).edgeSet
      exact h

end ErdosProblems.AntiRamseyPathFiveComponents

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- A component on at most three vertices has at most one edge per vertex. -/
theorem small_component_edge_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : Fintype.card V ≤ 3) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  have hchoose := G.card_edgeFinset_le_card_choose_two
  have hlimit : (Fintype.card V).choose 2 ≤ Fintype.card V := by
    interval_cases hcard : Fintype.card V <;> norm_num at *
  exact hchoose.trans hlimit

/-- If all components with at least five vertices and all four-vertex
components satisfy `edges ≤ vertices`, so does the whole graph. -/
theorem edge_le_vertex_of_component_bounds {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlarge : ∀ C : G.ConnectedComponent,
      5 ≤ Fintype.card C.supp →
      Nat.card C.toSimpleGraph.edgeSet ≤ Fintype.card C.supp)
    (hfour : ∀ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 → Nat.card C.toSimpleGraph.edgeSet ≤ 4) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  rw [edge_card_eq_sum_component_edge_card G,
    vertex_card_eq_sum_component_card G]
  apply Finset.sum_le_sum
  intro C _
  by_cases h5 : 5 ≤ Fintype.card C.supp
  · exact hlarge C h5
  by_cases h4 : Fintype.card C.supp = 4
  · simpa [h4] using hfour C h4
  have hsmall : Fintype.card C.supp ≤ 3 := by omega
  have hcardSupp : Fintype.card C = Fintype.card C.supp :=
    Fintype.card_congr (Equiv.refl _)
  have hsmallC : Fintype.card C ≤ 3 := by
    rw [hcardSupp]
    exact hsmall
  have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card]
    exact C.toSimpleGraph.card_edgeSet
  rw [hcard]
  rw [← hcardSupp]
  exact small_component_edge_le_card C.toSimpleGraph hsmallC

end ErdosProblems.AntiRamseyPathFiveComponents

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A nonempty vertex set closed under adjacency is the entire vertex set of
a connected graph. -/
theorem connected_closed_set_eq_univ {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {S : Set V} (a : V) (ha : a ∈ S)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) : S = Set.univ := by
  have walk_closed : ∀ {u v : V}, (p : G.Walk u v) → u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | cons hadj p ih => exact fun hu => ih (hclosed _ hu _ hadj)
  ext v
  constructor
  · intro _
    trivial
  · intro _
    exact (hconn a v).elim fun p => walk_closed p ha

/-- Five distinct vertices joined consecutively form a forbidden `P₅` copy. -/
theorem no_five_vertex_path {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d e : V)
    (hne : [a, b, c, d, e].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e) : False := by
  let p : G.Walk a e := .cons hab (.cons hbc (.cons hcd (.cons hde .nil)))
  have hp : p.IsPath := by
    simpa [p, Walk.isPath_def] using hne
  have hcopy : (pathGraph 5) ⊑ G := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- In a `P₅`-free graph, a fifth vertex cannot join either endpoint of a
four-vertex path, or both of its two interior vertices. -/
theorem p4_external_vertex_restrictions {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v : V)
    (hne : [a, b, c, d, v].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    ¬ G.Adj v a ∧ ¬ G.Adj v d ∧ ¬ (G.Adj v b ∧ G.Adj v c) := by
  have hperm₁ : [v, a, b, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₂ : [a, b, c, d, v].Nodup := hne
  have hperm₃ : [a, b, v, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  refine ⟨?_, ?_, ?_⟩
  · intro hva
    exact no_five_vertex_path hfree v a b c d hperm₁ hva hab hbc hcd
  · intro hvd
    exact no_five_vertex_path hfree a b c d v hperm₂ hab hbc hcd hvd.symm
  · rintro ⟨hvb, hvc⟩
    exact no_five_vertex_path hfree a b v c d hperm₃ hab hvb.symm hvc hcd

/-- An external vertex joined to either interior vertex of a four-vertex path
cannot have an edge to a second external vertex in a `P₅`-free graph. -/
theorem p4_external_neighbor_has_no_external_edge {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v w : V)
    (hne : [a, b, c, d, v, w].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hcenter : G.Adj v b ∨ G.Adj v c) : ¬ G.Adj v w := by
  intro hvw
  rcases hcenter with hvb | hvc
  · have hperm : [w, v, b, c, d].Nodup := by
      have hpair := hne
      simp [List.nodup_cons, List.mem_cons, not_or, eq_comm] at hpair ⊢
      tauto
    exact no_five_vertex_path hfree w v b c d hperm hvw.symm hvb hbc hcd
  · have hperm : [w, v, c, b, a].Nodup := by
      have hpair := hne
      simp [List.nodup_cons, List.mem_cons, not_or, eq_comm] at hpair ⊢
      tauto
    exact no_five_vertex_path hfree w v c b a hperm hvw.symm hvc hbc.symm hab.symm

/-- An external vertex adjacent to an interior point rules out the chord
between the path endpoints.  If it joins `b`, it also rules out `a-c`; if it
joins `c`, it rules out `b-d`. -/
theorem p4_external_vertex_forbids_chords {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (a b c d v : V)
    (hne : [a, b, c, d, v].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    (G.Adj v b → ¬ G.Adj a c) ∧
    (G.Adj v c → ¬ G.Adj b d) ∧
    ((G.Adj v b ∨ G.Adj v c) → ¬ G.Adj a d) := by
  have hperm₁ : [v, b, a, c, d].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₂ : [v, c, d, b, a].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₃ : [v, b, c, d, a].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  have hperm₄ : [v, c, d, a, b].Nodup := by
    simpa [List.nodup_cons, List.mem_cons, not_or, eq_comm,
      and_assoc, and_left_comm, and_comm] using hne
  refine ⟨?_, ?_, ?_⟩
  · intro hvb hac
    exact no_five_vertex_path hfree v b a c d hperm₁ hvb hab.symm hac hcd
  · intro hvc hbd
    exact no_five_vertex_path hfree v c d b a hperm₂ hvc hcd hbd.symm hab.symm
  · intro hcenter had
    rcases hcenter with hvb | hvc
    · exact no_five_vertex_path hfree v b c d a hperm₃ hvb hbc hcd had.symm
    · exact no_five_vertex_path hfree v c d a b hperm₄ hvc hcd had.symm hab

set_option maxHeartbeats 800000

/-- In a connected `P₅`-free graph, every vertex outside a fixed four-vertex
path is directly adjacent to exactly one of its two interior vertices.
The uniqueness uses `p4_external_vertex_restrictions`. -/
theorem p4_external_vertex_attached_to_center {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d v : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    G.Adj v b ∨ G.Adj v c := by
  let S : Set V := {x | x = a ∨ x = b ∨ x = c ∨ x = d ∨ G.Adj b x ∨ G.Adj c x}
  have hS : S = Set.univ := by
    apply connected_closed_set_eq_univ hconn a (show a ∈ S by simp [S])
    intro u hu w huw
    change u = a ∨ u = b ∨ u = c ∨ u = d ∨ G.Adj b u ∨ G.Adj c u at hu
    change w = a ∨ w = b ∨ w = c ∨ w = d ∨ G.Adj b w ∨ G.Adj c w
    by_cases hwcore : w = a ∨ w = b ∨ w = c ∨ w = d
    · tauto
    have hne_w : [a, b, c, d, w].Nodup := by
      have hpair := hpath
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    by_cases hucore : u = a ∨ u = b ∨ u = c ∨ u = d
    · rcases hucore with ha | hb | hc | hd
      · have hwa : G.Adj w a := by simpa [ha] using huw.symm
        exact False.elim ((p4_external_vertex_restrictions hfree a b c d w
          hne_w hab hbc hcd).1 hwa)
      · have hbw : G.Adj b w := by simpa [hb] using huw
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hbw))))
      · have hcw : G.Adj c w := by simpa [hc] using huw
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcw))))
      · have hwd : G.Adj w d := by simpa [hd] using huw.symm
        exact False.elim ((p4_external_vertex_restrictions hfree a b c d w
          hne_w hab hbc hcd).2.1 hwd)
    have hcenter : G.Adj u b ∨ G.Adj u c := by
      rcases hu with ha | hb | hc | hd | hub | huc
      · exact False.elim (hucore (Or.inl ha))
      · exact False.elim (hucore (Or.inr (Or.inl hb)))
      · exact False.elim (hucore (Or.inr (Or.inr (Or.inl hc))))
      · exact False.elim (hucore (Or.inr (Or.inr (Or.inr hd))))
      · exact Or.inl hub.symm
      · exact Or.inr huc.symm
    have hne_uw : [a, b, c, d, u, w].Nodup := by
      have hpair := hpath
      have hneq := huw.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    exact False.elim ((p4_external_neighbor_has_no_external_edge hfree
      a b c d u w hne_uw hab hbc hcd hcenter) huw)
  have hvS : v ∈ S := by rw [hS]; trivial
  change v = a ∨ v = b ∨ v = c ∨ v = d ∨ G.Adj b v ∨ G.Adj c v at hvS
  rcases hvS with ha | hb | hc | hd | hbv | hcv
  · exact False.elim (hv.1 ha)
  · exact False.elim (hv.2.1 hb)
  · exact False.elim (hv.2.2.1 hc)
  · exact False.elim (hv.2.2.2 hd)
  · exact Or.inl hbv.symm
  · exact Or.inr hcv.symm

/-- Every vertex outside a four-vertex path in a connected `P₅`-free graph
has exactly one neighbor, namely one of the two path interior vertices. -/
theorem p4_external_vertex_is_leaf {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d v : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d) :
    ∃ z : V, (z = b ∨ z = c) ∧ G.Adj v z ∧ ∀ w, G.Adj v w → w = z := by
  have hfive : [a, b, c, d, v].Nodup := by
    have hpair := hpath
    simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
    tauto
  have hrestr := p4_external_vertex_restrictions hfree a b c d v hfive hab hbc hcd
  have hcenter := p4_external_vertex_attached_to_center
    hfree hconn a b c d v hpath hab hbc hcd hv
  have honly : ∀ w, G.Adj v w → w = b ∨ w = c := by
    intro w hvw
    by_cases hwcore : w = a ∨ w = b ∨ w = c ∨ w = d
    · rcases hwcore with ha | hb | hc | hd
      · have hva : G.Adj v a := by simpa [ha] using hvw
        exact False.elim (hrestr.1 hva)
      · exact Or.inl hb
      · exact Or.inr hc
      · have hvd : G.Adj v d := by simpa [hd] using hvw
        exact False.elim (hrestr.2.1 hvd)
    have hne_uw : [a, b, c, d, v, w].Nodup := by
      have hpair := hpath
      have hneq := hvw.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
      tauto
    exact False.elim ((p4_external_neighbor_has_no_external_edge hfree
      a b c d v w hne_uw hab hbc hcd hcenter) hvw)
  rcases hcenter with hvb | hvc
  · refine ⟨b, Or.inl rfl, hvb, ?_⟩
    intro w hvw
    rcases honly w hvw with hb | hc
    · exact hb
    · have hvc : G.Adj v c := by simpa [hc] using hvw
      exact False.elim (hrestr.2.2 ⟨hvb, hvc⟩)
  · refine ⟨c, Or.inr rfl, hvc, ?_⟩
    intro w hvw
    rcases honly w hvw with hb | hc
    · have hvb : G.Adj v b := by simpa [hb] using hvw
      exact False.elim (hrestr.2.2 ⟨hvb, hvc⟩)
    · exact hc

end ErdosProblems.AntiRamseyPathFiveExtremal

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A non-diagonal edge with both endpoints in four named vertices is one of
the six possible unordered pairs. -/
theorem edge_in_four_vertices {V : Type*} [DecidableEq V]
    (a b c d : V) (e : Sym2 V)
    (he : e.toFinset ⊆ ({a, b, c, d} : Finset V))
    (hne : ¬e.IsDiag) :
    e = s(a, b) ∨ e = s(a, c) ∨ e = s(a, d) ∨
    e = s(b, c) ∨ e = s(b, d) ∨ e = s(c, d) := by
  induction e using Sym2.inductionOn with
  | hf u w =>
    have hu : u ∈ ({a, b, c, d} : Finset V) := he (by simp)
    have hw : w ∈ ({a, b, c, d} : Finset V) := he (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
    have huw : u ≠ w := by simpa [Sym2.mk_isDiag_iff] using hne
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl | rfl <;>
      simp_all [Sym2.eq_swap]

/-- A fifth vertex attached to an interior point of a `P₄` forces the
four-vertex core to have at most four edges. -/
theorem p4_core_edges_le_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d x : V)
    (hfree : (pathGraph 5).Free G)
    (hpath : [a, b, c, d].Nodup)
    (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hcenter : G.Adj x b ∨ G.Adj x c) :
    (G.edgeFinset.filter fun e => e.toFinset ⊆ ({a, b, c, d} : Finset V)).card ≤ 4 := by
  classical
  have hfive : [a, b, c, d, x].Nodup := by
    have hpair := hpath
    simp [List.nodup_cons, List.mem_cons, not_or] at hpair ⊢
    tauto
  have hchords := p4_external_vertex_forbids_chords
    hfree a b c d x hfive hab hbc hcd
  rcases hcenter with hxb | hxc
  · let allowed : Finset (Sym2 V) := {s(a, b), s(b, c), s(c, d), s(b, d)}
    have hsubset : (G.edgeFinset.filter fun e =>
        e.toFinset ⊆ ({a, b, c, d} : Finset V)) ⊆ allowed := by
      intro e he
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
      have hecore := (Finset.mem_filter.mp he).2
      have hcase := edge_in_four_vertices a b c d e hecore
        (G.not_isDiag_of_mem_edgeFinset heG)
      rcases hcase with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
      · simp [allowed, h₁]
      · have hac : G.Adj a c := by
          simpa only [h₂, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.1 hxb) hac)
      · have had : G.Adj a d := by
          simpa only [h₃, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.2 (Or.inl hxb)) had)
      · simp [allowed, h₄]
      · simp [allowed, h₅]
      · simp [allowed, h₆]
    calc
      _ ≤ allowed.card := Finset.card_le_card hsubset
      _ ≤ 4 := Finset.card_le_four
  · let allowed : Finset (Sym2 V) := {s(a, b), s(b, c), s(c, d), s(a, c)}
    have hsubset : (G.edgeFinset.filter fun e =>
        e.toFinset ⊆ ({a, b, c, d} : Finset V)) ⊆ allowed := by
      intro e he
      have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
      have hecore := (Finset.mem_filter.mp he).2
      have hcase := edge_in_four_vertices a b c d e hecore
        (G.not_isDiag_of_mem_edgeFinset heG)
      rcases hcase with h₁ | h₂ | h₃ | h₄ | h₅ | h₆
      · simp [allowed, h₁]
      · simp [allowed, h₂]
      · have had : G.Adj a d := by
          simpa only [h₃, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.2 (Or.inr hxc)) had)
      · simp [allowed, h₄]
      · have hbd : G.Adj b d := by
          simpa only [h₅, G.mem_edgeFinset, G.mem_edgeSet] using heG
        exact False.elim ((hchords.2.1 hxc) hbd)
      · simp [allowed, h₆]
    calc
      _ ≤ allowed.card := Finset.card_le_card hsubset
      _ ≤ 4 := Finset.card_le_four

end ErdosProblems.AntiRamseyPathFiveExtremal

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- If the edges inside a finite core number at most its vertices and every
outside vertex is a leaf attached to the core, then the entire graph has at
most one edge per vertex. -/
theorem edge_count_of_core_and_leaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hcore : (G.edgeFinset.filter fun e => e.toFinset ⊆ C).card ≤ C.card)
    (hleaf : ∀ v : V, v ∉ C →
      ∃ z : V, z ∈ C ∧ G.Adj v z ∧ ∀ w : V, G.Adj v w → w = z) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  let Ecore : Finset (Sym2 V) := G.edgeFinset.filter fun e => e.toFinset ⊆ C
  let Eout : Finset (Sym2 V) := G.edgeFinset.filter fun e => ¬e.toFinset ⊆ C
  let O := {v : V // v ∉ C}
  let leafEdge : O → Sym2 V := fun v => s(v.1, Classical.choose (hleaf v.1 v.2))
  have hcover : Eout ⊆ (Finset.univ : Finset O).image leafEdge := by
    intro e he
    have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
    have heOutside : ¬e.toFinset ⊆ C := (Finset.mem_filter.mp he).2
    induction e using Sym2.inductionOn with
    | hf u w =>
      have hadj : G.Adj u w := by
        simpa only [G.mem_edgeFinset, G.mem_edgeSet] using heG
      have hout : u ∉ C ∨ w ∉ C := by
        by_contra h
        have hmem : u ∈ C ∧ w ∈ C := by tauto
        apply heOutside
        intro y hy
        have hyuw : y = u ∨ y = w := by simpa [Sym2.toFinset_mk_eq] using hy
        rcases hyuw with rfl | rfl
        · exact hmem.1
        · exact hmem.2
      rcases hout with hu | hw
      · refine Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, ?_⟩
        have huniq := (Classical.choose_spec (hleaf u hu)).2.2
        have hwu := huniq w hadj
        simp [leafEdge, hwu]
      · refine Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_univ _, ?_⟩
        have huniq := (Classical.choose_spec (hleaf w hw)).2.2
        have huw := huniq u hadj.symm
        simp [leafEdge, huw, Sym2.eq_swap]
  have hOcard : (Finset.univ : Finset O).card = (Finset.univ \ C).card := by
    simp [O, Fintype.card_subtype, Finset.sdiff_eq_filter]
  have houtCard : Eout.card ≤ (Finset.univ \ C).card := by
    calc
      Eout.card ≤ ((Finset.univ : Finset O).image leafEdge).card :=
        Finset.card_le_card hcover
      _ ≤ (Finset.univ : Finset O).card := Finset.card_image_le
      _ = (Finset.univ \ C).card := hOcard
  have hsplit : Ecore.card + Eout.card = G.edgeFinset.card := by
    simpa [Ecore, Eout] using
      (Finset.card_filter_add_card_filter_not (s := G.edgeFinset)
        (p := fun e : Sym2 V => e.toFinset ⊆ C))
  calc
    G.edgeFinset.card = Ecore.card + Eout.card := hsplit.symm
    _ ≤ C.card + (Finset.univ \ C).card := Nat.add_le_add hcore houtCard
    _ = Fintype.card V := by
      simpa [add_comm] using
        (Finset.card_sdiff_add_card_eq_card (s := C) (t := Finset.univ)
          (Finset.subset_univ C))

end ErdosProblems.AntiRamseyPathFiveExtremal

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A connected `P₅`-free graph on at least five vertices has at most one
edge per vertex if it contains a four-vertex path. -/
theorem p4_connected_p5_free_edges_le_card {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 5 ≤ Fintype.card V)
    (hfree : (pathGraph 5).Free G) (hconn : G.Connected)
    (a b c d : V) (hpath : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  let C : Finset V := {a, b, c, d}
  have hCcard : C.card = 4 := by
    simpa [C, List.toFinset_cons] using
      (List.toFinset_card_of_nodup hpath)
  have hlt : C.card < (Finset.univ : Finset V).card := by
    simpa [hCcard] using
      (Nat.lt_of_lt_of_le (by decide : 4 < 5) hcard)
  obtain ⟨x, _, hxC⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := C) (t := Finset.univ) hlt
  have hx : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    have hx' : ¬(x = a ∨ x = b ∨ x = c ∨ x = d) := by
      simpa [C] using hxC
    tauto
  have hcenter : G.Adj x b ∨ G.Adj x c :=
    p4_external_vertex_attached_to_center
      hfree hconn a b c d x hpath hab hbc hcd hx
  have hcore :
      (G.edgeFinset.filter fun e => e.toFinset ⊆ C).card ≤ C.card := by
    change (G.edgeFinset.filter fun e =>
      e.toFinset ⊆ ({a, b, c, d} : Finset V)).card ≤ C.card
    rw [hCcard]
    exact p4_core_edges_le_four G a b c d x hfree hpath hx hab hbc hcd hcenter
  have hleaf : ∀ v : V, v ∉ C →
      ∃ z : V, z ∈ C ∧ G.Adj v z ∧ ∀ w : V, G.Adj v w → w = z := by
    intro v hvC
    have hv : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
      have hv' : ¬(v = a ∨ v = b ∨ v = c ∨ v = d) := by
        simpa [C] using hvC
      tauto
    obtain ⟨z, hz, hvz, huniq⟩ :=
      p4_external_vertex_is_leaf hfree hconn a b c d v hpath hab hbc hcd hv
    refine ⟨z, ?_, hvz, huniq⟩
    rcases hz with rfl | rfl <;> simp [C]
  exact edge_count_of_core_and_leaves G C hcore hleaf

end ErdosProblems.AntiRamseyPathFiveExtremal

namespace ErdosProblems.AntiRamseyPathFourFree

open SimpleGraph

/-- Four distinct consecutive vertices contradict `pathGraph 4`-freeness. -/
theorem no_four_vertex_path {V : Type*} {G : SimpleGraph V}
    (hfree : (pathGraph 4).Free G) (a b c d : V)
    (hne : [a, b, c, d].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) : False := by
  let p : G.Walk a d := .cons hab (.cons hbc (.cons hcd .nil))
  have hp : p.IsPath := by
    simpa [p, Walk.isPath_def] using hne
  have hcopy : (pathGraph 4) ⊑ G := by
    simpa [p] using hp.isContained_pathGraph
  exact hfree hcopy

/-- An adjacency-closed nonempty set in a connected graph is all vertices. -/
theorem connected_closed_set_eq_univ {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) {S : Set V} (a : V) (ha : a ∈ S)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) : S = Set.univ := by
  have walk_closed : ∀ {u v : V}, (p : G.Walk u v) → u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | cons hadj p ih => exact fun hu => ih (hclosed _ hu _ hadj)
  ext v
  constructor
  · intro _
    trivial
  · intro _
    exact (hconn a v).elim fun p => walk_closed p ha

/-- In a connected graph with at least three vertices there is a vertex
with two distinct neighbors. -/
theorem connected_exists_two_neighbors {n : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (hconn : G.Connected) :
    ∃ b a c : Fin n, a ≠ c ∧ G.Adj b a ∧ G.Adj b c := by
  let x : Fin n := ⟨0, by omega⟩
  let y : Fin n := ⟨1, by omega⟩
  let z : Fin n := ⟨2, by omega⟩
  have hxy : x ≠ y := by simp [x, y]
  have hxz : x ≠ z := by simp [x, z]
  have hyz : y ≠ z := by simp [y, z]
  have pair_of_nonadjacent {u v : Fin n} (huv : u ≠ v)
      (hnot : ¬ G.Adj u v) :
      ∃ b a c : Fin n, a ≠ c ∧ G.Adj b a ∧ G.Adj b c := by
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
    have hdist : 1 < G.dist u v :=
      (hconn u v).one_lt_dist_of_ne_of_not_adj huv hnot
    obtain ⟨w, b, c, hwb, hbc, _, hwc⟩ := p.exists_adj_adj_not_adj_ne hp hdist
    exact ⟨b, w, c, hwc, hwb.symm, hbc⟩
  by_cases hxyadj : G.Adj x y
  · by_cases hxzadj : G.Adj x z
    · exact ⟨x, y, z, hyz, hxyadj, hxzadj⟩
    · exact pair_of_nonadjacent hxz hxzadj
  · exact pair_of_nonadjacent hxy hxyadj

/-- A vertex with two neighbors has a universal closed neighborhood in a
connected `P₄`-free graph. -/
theorem universal_of_two_neighbors {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (hfree : (pathGraph 4).Free G)
    (b a c : V) (hac : a ≠ c) (hba : G.Adj b a) (hbc : G.Adj b c) :
    ∀ v : V, v ≠ b → G.Adj b v := by
  let S : Set V := {v | v = b ∨ G.Adj b v}
  have hbS : b ∈ S := Or.inl rfl
  have hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S := by
    intro u hu v huv
    by_cases hvb : v = b
    · exact Or.inl hvb
    by_cases hbv : G.Adj b v
    · exact Or.inr hbv
    rcases hu with hub | hbu
    · subst u
      exact False.elim (hbv huv)
    have hub : u ≠ b := hbu.ne'
    by_cases hua : u = a
    · have hnodup : [c, b, u, v].Nodup := by
        have hcb : c ≠ b := hbc.ne'
        have hcu : c ≠ u := by simpa [hua] using hac.symm
        have hcv : c ≠ v := by intro h; subst v; exact hbv hbc
        have huvne : u ≠ v := huv.ne
        simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
        tauto
      exact False.elim (no_four_vertex_path hfree c b u v
        hnodup hbc.symm hbu huv)
    · have hnodup : [a, b, u, v].Nodup := by
        have hab : a ≠ b := hba.ne'
        have hau : a ≠ u := Ne.symm hua
        have hav : a ≠ v := by intro h; subst v; exact hbv hba
        have huvne : u ≠ v := huv.ne
        simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
        tauto
      exact False.elim (no_four_vertex_path hfree a b u v
        hnodup hba.symm hbu huv)
  have hS : S = Set.univ := connected_closed_set_eq_univ hconn b hbS hclosed
  intro v hvb
  have hvS : v ∈ S := by rw [hS]; trivial
  rcases hvS with hv | hv
  · exact False.elim (hvb hv)
  · exact hv

/-- The connected `P₄`-free case is a spanning star and has fewer edges
than vertices. The hypothesis `4 ≤ n` excludes a standalone triangle. -/
theorem connected_path_four_free_edge_count {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card + 1 = n := by
  classical
  obtain ⟨b, a, c, hac, hba, hbc⟩ :=
    connected_exists_two_neighbors (by omega : 3 ≤ n) G hconn
  have huni := universal_of_two_neighbors hconn hfree b a c hac hba hbc
  have hex (u v : Fin n) : ∃ t : Fin n, t ≠ b ∧ t ≠ u ∧ t ≠ v := by
    have hcard : ({b, u, v} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    by_contra h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {b, u, v} := by
      intro t _
      by_contra ht
      exact h ⟨t, by simpa using ht⟩
    have hshort : n ≤ 3 := by
      simpa using (Finset.card_le_card hsub).trans hcard
    omega
  have hle : G ≤ starGraph b := by
    intro u v huv
    by_cases hub : u = b
    · exact starGraph_adj.mpr ⟨huv.ne, Or.inl hub⟩
    by_cases hvb : v = b
    · exact starGraph_adj.mpr ⟨huv.ne, Or.inr hvb⟩
    obtain ⟨t, htb, htu, htv⟩ := hex u v
    have hnodup : [t, b, u, v].Nodup := by
      have hbu : b ≠ u := Ne.symm hub
      have hbv : b ≠ v := Ne.symm hvb
      have huvne : u ≠ v := huv.ne
      simp [List.nodup_cons, List.mem_cons, not_or] at ⊢
      tauto
    exact False.elim (no_four_vertex_path hfree t b u v hnodup
      (huni t htb).symm (huni u hub) huv)
  have hstar : G = starGraph b := by
    apply le_antisymm hle
    intro u v huv
    rcases starGraph_adj.mp huv with ⟨hne, hub | hvb⟩
    · subst u
      exact huni v hne.symm
    · subst v
      exact (huni u hne).symm
  have hcard_eq : G.edgeFinset.card = (starGraph b).edgeFinset.card := by
    exact congrArg Finset.card (edgeFinset_inj.mpr hstar)
  calc
    G.edgeFinset.card + 1 = (starGraph b).edgeFinset.card + 1 := by rw [hcard_eq]
    _ = n := by simpa using (isTree_starGraph b).card_edgeFinset

theorem connected_path_four_free_edge_le {n : ℕ} (hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card ≤ n := by
  have h := connected_path_four_free_edge_count (by omega : 4 ≤ n) G hconn hfree
  omega

end ErdosProblems.AntiRamseyPathFourFree

namespace ErdosProblems.AntiRamseyPathFourFree

open SimpleGraph

/-- The exact no-`P₄` star edge count for any finite vertex carrier. This is
the form usable for a connected component represented as a subtype. -/
theorem connected_path_four_free_edge_count_finite {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 4 ≤ Fintype.card V) (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card + 1 = Fintype.card V := by
  classical
  let H : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
  let e : G ≃g H := G.overFinIso rfl
  have hconnH : H.Connected := e.connected_iff.mp hconn
  have hfreeH : (pathGraph 4).Free H := (free_congr_right e).mp hfree
  have hcount : H.edgeFinset.card + 1 = Fintype.card V :=
    connected_path_four_free_edge_count hn H hconnH hfreeH
  have hcard : G.edgeFinset.card = H.edgeFinset.card := e.card_edgeFinset_eq
  omega

/-- The component-count interface used by the connected `P₅` argument. -/
theorem connected_path_four_free_edge_le_finite {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 5 ≤ Fintype.card V) (hconn : G.Connected)
    (hfree : (pathGraph 4).Free G) :
    G.edgeFinset.card ≤ Fintype.card V := by
  have h := connected_path_four_free_edge_count_finite G (by omega : 4 ≤ Fintype.card V)
    hconn hfree
  omega

end ErdosProblems.AntiRamseyPathFourFree

namespace ErdosProblems.AntiRamseyPathFiveExtremal

open SimpleGraph

/-- A connected `P₅`-free graph on at least five vertices has at most one
edge per vertex. -/
theorem connected_path_five_free_edge_le_finite {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 5 ≤ Fintype.card V)
    (hconn : G.Connected) (hfree : (pathGraph 5).Free G) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  by_cases hfour : (pathGraph 4).Free G
  · exact ErdosProblems.AntiRamseyPathFourFree.connected_path_four_free_edge_le_finite
      G hn hconn hfour
  · have hcopy : (pathGraph 4) ⊑ G := not_free.mp hfour
    obtain ⟨f⟩ := hcopy
    have hbase : ([0, 1, 2, 3] : List (Fin 4)).Nodup := by decide
    have hpath : [f (0 : Fin 4), f (1 : Fin 4), f (2 : Fin 4), f (3 : Fin 4)].Nodup := by
      simpa using (List.Nodup.map f.injective hbase)
    have hab : G.Adj (f (0 : Fin 4)) (f (1 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    have hbc : G.Adj (f (1 : Fin 4)) (f (2 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    have hcd : G.Adj (f (2 : Fin 4)) (f (3 : Fin 4)) :=
      f.toHom.map_adj ((pathGraph_adj).2 (Or.inl (by decide)))
    exact p4_connected_p5_free_edges_le_card G hn hfree hconn
      (f (0 : Fin 4)) (f (1 : Fin 4)) (f (2 : Fin 4)) (f (3 : Fin 4))
      hpath hab hbc hcd

end ErdosProblems.AntiRamseyPathFiveExtremal

namespace ErdosProblems.AntiRamseyPathFiveComponents

open SimpleGraph

/-- A `P₅`-free graph on at least five vertices with more edges than vertices
has a four-vertex connected component with at least five edges. -/
theorem exists_dense_four_component {n : ℕ} (_hn : 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : (pathGraph 5).Free G) (hmore : n < G.edgeFinset.card) :
    ∃ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 ∧ 5 ≤ Nat.card C.toSimpleGraph.edgeSet := by
  classical
  by_contra hnone
  have hfour : ∀ C : G.ConnectedComponent,
      Fintype.card C.supp = 4 → Nat.card C.toSimpleGraph.edgeSet ≤ 4 := by
    intro C hm
    by_contra hle
    have hfive : 5 ≤ Nat.card C.toSimpleGraph.edgeSet := by omega
    exact hnone ⟨C, hm, hfive⟩
  have hlarge : ∀ C : G.ConnectedComponent,
      5 ≤ Fintype.card C.supp →
      Nat.card C.toSimpleGraph.edgeSet ≤ Fintype.card C.supp := by
    intro C hm
    have hcopy : C.toSimpleGraph ⊑ G := by
      refine ⟨{ toHom := C.toSimpleGraph_hom, injective' := ?_ }⟩
      intro u v huv
      exact Subtype.coe_injective huv
    have hfreeC : (pathGraph 5).Free C.toSimpleGraph := by
      intro hpath
      exact hfree (hpath.trans hcopy)
    have hcardSupp : Fintype.card C = Fintype.card C.supp :=
      Fintype.card_congr (Equiv.refl _)
    have hmC : 5 ≤ Fintype.card C := by
      rw [hcardSupp]
      exact hm
    have hcard : Nat.card C.toSimpleGraph.edgeSet = C.toSimpleGraph.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card]
      exact C.toSimpleGraph.card_edgeSet
    rw [hcard]
    have hbound := ErdosProblems.AntiRamseyPathFiveExtremal.connected_path_five_free_edge_le_finite
      C.toSimpleGraph hmC C.connected_toSimpleGraph hfreeC
    rw [hcardSupp] at hbound
    exact hbound
  have hbound := edge_le_vertex_of_component_bounds G hlarge hfour
  have hbound' : G.edgeFinset.card ≤ n := by simpa using hbound
  omega

end ErdosProblems.AntiRamseyPathFiveComponents

namespace ErdosProblems.AntiRamseyRepresentative

open SimpleGraph

variable {n q : ℕ}

/-- The edge chosen for color `k` by a right inverse to a surjective coloring. -/
noncomputable def chosenEdge (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : (⊤ : SimpleGraph (Fin n)).edgeSet :=
  Function.surjInv hχ k

theorem chosenEdge_color (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : χ (chosenEdge χ hχ k) = k :=
  Function.surjInv_eq hχ k

/-- A graph on all `n` vertices containing exactly one chosen edge for each color. -/
noncomputable def representativeGraph (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Set.range fun k : Fin q => (chosenEdge χ hχ k).val)

theorem chosenEdge_not_diag (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) :
    ¬ ((chosenEdge χ hχ k).val : Sym2 (Fin n)).IsDiag :=
  (⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeSet (chosenEdge χ hχ k).property

theorem representativeGraph_edgeSet (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    (representativeGraph χ hχ).edgeSet =
      Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
  rw [representativeGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact fun he => he.1
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, rfl⟩, chosenEdge_not_diag χ hχ k⟩

noncomputable instance representativeGraph_edgeSet_fintype
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ) :
    Fintype (representativeGraph χ hχ).edgeSet := Fintype.ofFinite _

/-- The chosen edge as an edge of the representative graph. -/
noncomputable def chosenRepresentativeEdge (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) : (representativeGraph χ hχ).edgeSet :=
  ⟨(chosenEdge χ hχ k).val, by
    rw [representativeGraph_edgeSet]
    exact ⟨k, rfl⟩⟩

theorem chosenRepresentativeEdge_color (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (k : Fin q) :
    χ ⟨(chosenRepresentativeEdge χ hχ k).val,
      by exact (chosenEdge χ hχ k).property⟩ = k := by
  exact chosenEdge_color χ hχ k

/-- Restriction of the complete coloring to the representative graph. -/
def restrictedColor (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : (representativeGraph χ hχ).edgeSet → Fin q :=
  fun e => χ ⟨e.val, by
    exact SimpleGraph.edgeSet_mono le_top e.property⟩

/-- Distinct edges of the representative graph have distinct colors. -/
theorem restrictedColor_injective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    Function.Injective (restrictedColor χ hχ) := by
  intro e₁ e₂ heq
  have he₁ : e₁.val ∈ Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
    rw [← representativeGraph_edgeSet χ hχ]
    exact e₁.property
  have he₂ : e₂.val ∈ Set.range (fun k : Fin q => (chosenEdge χ hχ k).val) := by
    rw [← representativeGraph_edgeSet χ hχ]
    exact e₂.property
  obtain ⟨k₁, hk₁⟩ := he₁
  obtain ⟨k₂, hk₂⟩ := he₂
  have hc₁ : restrictedColor χ hχ e₁ = k₁ := by
    have hval : e₁.val = (chosenEdge χ hχ k₁).val := hk₁.symm
    simpa [restrictedColor, hval] using chosenEdge_color χ hχ k₁
  have hc₂ : restrictedColor χ hχ e₂ = k₂ := by
    have hval : e₂.val = (chosenEdge χ hχ k₂).val := hk₂.symm
    simpa [restrictedColor, hval] using chosenEdge_color χ hχ k₂
  have hk : k₁ = k₂ := hc₁.symm.trans (heq.trans hc₂)
  apply Subtype.ext
  calc
    e₁.val = (chosenEdge χ hχ k₁).val := hk₁.symm
    _ = (chosenEdge χ hχ k₂).val := by rw [hk]
    _ = e₂.val := hk₂

/-- Every color occurs once on the representative graph. -/
theorem restrictedColor_surjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    Function.Surjective (restrictedColor χ hχ) := by
  intro k
  refine ⟨chosenRepresentativeEdge χ hχ k, ?_⟩
  simpa [restrictedColor] using chosenRepresentativeEdge_color χ hχ k

/-- The representative graph has exactly `q` edges. -/
theorem representativeGraph_card_edgeFinset (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) :
    (representativeGraph χ hχ).edgeFinset.card = q := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let e : (representativeGraph χ hχ).edgeSet ≃ Fin q :=
    Equiv.ofBijective (restrictedColor χ hχ)
      ⟨restrictedColor_injective χ hχ, restrictedColor_surjective χ hχ⟩
  simpa using Fintype.card_congr e

/-- A copy in the representative graph becomes a rainbow copy in the complete graph. -/
theorem copy_in_representativeGraph_isRainbow {α : Type*} {H : SimpleGraph α}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (f : H.Copy (representativeGraph χ hχ)) :
    IsRainbow ((Copy.ofLE (representativeGraph χ hχ)
      (⊤ : SimpleGraph (Fin n)) le_top).comp f).toHom χ := by
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    (Copy.ofLE (representativeGraph χ hχ) (⊤ : SimpleGraph (Fin n)) le_top).comp f
  change Function.Injective (EdgeLabeling.pullback χ g.toHom)
  have hcolors (e : H.edgeSet) :
      EdgeLabeling.pullback χ g.toHom e = restrictedColor χ hχ (f.mapEdgeSet e) := by
    have hval : (g.toHom.mapEdgeSet e).val = (f.mapEdgeSet e).val := by
      simp [g, Copy.comp, Copy.ofLE, Hom.mapEdgeSet]
      rfl
    exact congrArg χ (Subtype.ext hval)
  intro e₁ e₂ hcolorsEq
  apply f.mapEdgeSet.injective
  exact restrictedColor_injective χ hχ
    ((hcolors e₁).symm.trans (hcolorsEq.trans (hcolors e₂)))

/-- A coloring with no rainbow `H` forces its representative graph to be `H`-free. -/
theorem representativeGraph_free {α : Type*} (H : SimpleGraph α)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f.toHom χ) :
    H.Free (representativeGraph χ hχ) := by
  intro hcopy
  obtain ⟨f⟩ := hcopy
  exact hno _ (copy_in_representativeGraph_isRainbow χ hχ f)

end ErdosProblems.AntiRamseyRepresentative

namespace ErdosProblems.AntiRamseyPathFiveTransfer

open SimpleGraph
open ErdosProblems.AntiRamseyRepresentative
open ErdosProblems.AntiRamseyPathFiveUpper

/-- The five edges of a diamond on named vertices `a,b,c,d`. Its missing
edge `a-b` is unrestricted. -/
def DiamondOn {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- The diamond edges `ac,ad,bc,bd,cd` at positions 0 through 4,
where the first index of `Fin 5` is reserved for the extra vertex. -/
def diamondIndex (i : Fin 5) : Sym2 (Fin 5) :=
  if i = 0 then s(1, 3)
  else if i = 1 then s(1, 4)
  else if i = 2 then s(2, 3)
  else if i = 3 then s(2, 4)
  else s(3, 4)

theorem diamondIndex_injective : Function.Injective diamondIndex := by
  decide

/-- The five edges inside a representative diamond as graph edge subtypes. -/
def representativeDiamondEdge {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) : (representativeGraph χ hχ).edgeSet :=
  if i = 0 then ⟨s(u 1, u 3), hd.1⟩
  else if i = 1 then ⟨s(u 1, u 4), hd.2.1⟩
  else if i = 2 then ⟨s(u 2, u 3), hd.2.2.1⟩
  else if i = 3 then ⟨s(u 2, u 4), hd.2.2.2.1⟩
  else ⟨s(u 3, u 4), hd.2.2.2.2⟩

theorem representativeDiamondEdge_val {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) :
    (representativeDiamondEdge χ hχ u hd i).val =
      Sym2.map u (diamondIndex i) := by
  fin_cases i <;>
    simp [representativeDiamondEdge, diamondIndex, Sym2.map_mk]

theorem representativeDiamondEdge_injective {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4)) :
    Function.Injective (representativeDiamondEdge χ hχ u hd) := by
  intro i j he
  apply diamondIndex_injective
  apply Sym2.map.injective hu
  calc
    Sym2.map u (diamondIndex i) =
        (representativeDiamondEdge χ hχ u hd i).val :=
      (representativeDiamondEdge_val χ hχ u hd i).symm
    _ = (representativeDiamondEdge χ hχ u hd j).val := congrArg Subtype.val he
    _ = Sym2.map u (diamondIndex j) :=
      representativeDiamondEdge_val χ hχ u hd j

theorem diamondEdgeColors_eq_restrictedColor {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) :
    diamondEdgeColors χ u hu i =
      restrictedColor χ hχ (representativeDiamondEdge χ hχ u hd i) := by
  fin_cases i <;>
    simp [diamondEdgeColors, representativeDiamondEdge, restrictedColor,
      EdgeLabeling.get]

/-- A five-vertex embedding whose four diamond vertices have five edges in
the one-edge-per-color representative graph yields a rainbow `P₅` copy. -/
theorem rainbow_path_five_of_representative_diamond_five {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hcolors : Function.Injective (diamondEdgeColors χ u hu) := by
    intro i j he
    apply representativeDiamondEdge_injective χ hχ u hu hd
    apply restrictedColor_injective χ hχ
    exact (diamondEdgeColors_eq_restrictedColor χ hχ u hu hd i).symm.trans
      (he.trans (diamondEdgeColors_eq_restrictedColor χ hχ u hu hd j))
  exact rainbow_path_five_of_rainbow_diamond χ u hu hcolors

/-- Four representative diamond vertices can be supplemented by a fifth
vertex when the host has at least five vertices. -/
theorem rainbow_path_five_of_representative_diamond_four {n q : ℕ}
    (hn : 5 ≤ n) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (u : Fin 4 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 0) (u 1) (u 2) (u 3)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hnot_surj : ¬Function.Surjective u := by
    intro hs
    have hcard : 4 = n := by
      simpa using Fintype.card_congr (Equiv.ofBijective u ⟨hu, hs⟩)
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin n, ∀ i : Fin 4, u i ≠ v := by
    by_contra h
    push Not at h
    apply hnot_surj
    intro v
    obtain ⟨i, hi⟩ := h v
    exact ⟨i, by simpa using hi⟩
  have hv_not_range : v ∉ Set.range u := by
    rintro ⟨i, hi⟩
    exact hv i hi
  let w : Fin 5 → Fin n := Fin.cons v u
  have hw : Function.Injective w :=
    Fin.cons_injective_of_injective hv_not_range hu
  have hw₁ : w 1 = u 0 := by
    change w (Fin.succ (0 : Fin 4)) = u 0
    simp only [w, Fin.cons_succ]
  have hw₂ : w 2 = u 1 := by
    change w (Fin.succ (1 : Fin 4)) = u 1
    simp only [w, Fin.cons_succ]
  have hw₃ : w 3 = u 2 := by
    change w (Fin.succ (2 : Fin 4)) = u 2
    simp only [w, Fin.cons_succ]
  have hw₄ : w 4 = u 3 := by
    change w (Fin.succ (3 : Fin 4)) = u 3
    simp only [w, Fin.cons_succ]
  have hdiamond :
      DiamondOn (representativeGraph χ hχ) (w 1) (w 2) (w 3) (w 4) := by
    simpa only [hw₁, hw₂, hw₃, hw₄] using hd
  exact rainbow_path_five_of_representative_diamond_five χ hχ w hw hdiamond

/-- A coloring with no rainbow five-vertex path has no injectively embedded
diamond among its representative edges, for every `n ≥ 5`. -/
theorem no_representative_diamond_of_no_rainbow_path_five {n q : ℕ}
    (hn : 5 ≤ n) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (u : Fin 4 → Fin n) (hu : Function.Injective u) :
    ¬DiamondOn (representativeGraph χ hχ) (u 0) (u 1) (u 2) (u 3) := by
  intro hd
  obtain ⟨f, hf⟩ := rainbow_path_five_of_representative_diamond_four hn χ hχ u hu hd
  exact hno f hf

end ErdosProblems.AntiRamseyPathFiveTransfer

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- The index `i : Fin 4` names the corresponding consecutive edge of `P₅`. -/
theorem path_five_adj_succ (i : Fin 4) :
    (pathGraph 5).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

/-- The `i`th edge of the path `P₅`. -/
def pathFiveEdge (i : Fin 4) : (pathGraph 5).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), path_five_adj_succ i⟩

theorem pathFiveEdge_injective : Function.Injective pathFiveEdge := by
  decide

/-- Among the four edges of a copied five-vertex path, at least two avoid any given vertex.
The indices `i, j : Fin 4` specify the edges from `Fin.castSucc i` to `Fin.succ i`. -/
theorem path_five_copy_two_edges_avoid_vertex {n : ℕ}
    (f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n))) (a : Fin n) :
    ∃ i j : Fin 4, i ≠ j ∧
      f (Fin.castSucc i) ≠ a ∧ f (Fin.succ i) ≠ a ∧
      f (Fin.castSucc j) ≠ a ∧ f (Fin.succ j) ≠ a := by
  by_cases h₀ : a = f (0 : Fin 5)
  · refine ⟨1, 2, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₀] using f.injective.ne (show (1 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (2 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (2 : Fin 5) ≠ 0 by decide)
    · simpa [h₀] using f.injective.ne (show (3 : Fin 5) ≠ 0 by decide)
  by_cases h₁ : a = f (1 : Fin 5)
  · refine ⟨2, 3, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₁] using f.injective.ne (show (2 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (3 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (3 : Fin 5) ≠ 1 by decide)
    · simpa [h₁] using f.injective.ne (show (4 : Fin 5) ≠ 1 by decide)
  by_cases h₂ : a = f (2 : Fin 5)
  · refine ⟨0, 3, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₂] using f.injective.ne (show (0 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (1 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (3 : Fin 5) ≠ 2 by decide)
    · simpa [h₂] using f.injective.ne (show (4 : Fin 5) ≠ 2 by decide)
  by_cases h₃ : a = f (3 : Fin 5)
  · refine ⟨0, 1, by decide, ?_, ?_, ?_, ?_⟩
    · simpa [h₃] using f.injective.ne (show (0 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (1 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (1 : Fin 5) ≠ 3 by decide)
    · simpa [h₃] using f.injective.ne (show (2 : Fin 5) ≠ 3 by decide)
  refine ⟨0, 1, by decide, ?_, ?_, ?_, ?_⟩
  · simpa using Ne.symm h₀
  · simpa using Ne.symm h₁
  · simpa using Ne.symm h₁
  · simpa using Ne.symm h₂

end ErdosProblems.AntiRamseyPathFive

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- Every copied five-vertex path has two edges colored zero by the star
construction, so it cannot be rainbow. -/
theorem starColor_noRainbowPathFive {n : ℕ} [NeZero n]
    (f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n))) :
    ¬ IsRainbow f.toHom (starColor n) := by
  intro hrainbow
  obtain ⟨i, j, hij, hai, hbi, haj, hbj⟩ :=
    path_five_copy_two_edges_avoid_vertex f (0 : Fin n)
  have hadj_i : (⊤ : SimpleGraph (Fin n)).Adj
      (f (Fin.castSucc i)) (f (Fin.succ i)) :=
    f.toHom.map_rel (path_five_adj_succ i)
  have hadj_j : (⊤ : SimpleGraph (Fin n)).Adj
      (f (Fin.castSucc j)) (f (Fin.succ j)) :=
    f.toHom.map_rel (path_five_adj_succ j)
  have hcolor_i : (EdgeLabeling.pullback (starColor n) f.toHom) (pathFiveEdge i) = 0 := by
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathFiveEdge] using
      starColor_get_nonincident (f (Fin.castSucc i)) (f (Fin.succ i)) hadj_i hai hbi
  have hcolor_j : (EdgeLabeling.pullback (starColor n) f.toHom) (pathFiveEdge j) = 0 := by
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathFiveEdge] using
      starColor_get_nonincident (f (Fin.castSucc j)) (f (Fin.succ j)) hadj_j haj hbj
  exact (pathFiveEdge_injective.ne hij)
    (hrainbow (hcolor_i.trans hcolor_j.symm))

theorem antiRamseyNum_pathGraph_five_ge_aux (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    n ≤ antiRamseyNum (pathGraph 5) n := by
  let S : Set ℕ :=
    {k | ∃ χ : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective χ ∧
      ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}
  have hB : BddAbove S := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro k hk
    obtain ⟨χ, hχ, _⟩ := hk
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : n ∈ S := by
    refine ⟨starColor n, starColor_surjective n hn, ?_⟩
    intro f
    exact starColor_noRainbowPathFive f
  change n ≤ sSup S
  exact le_csSup hB hmem

/-- Yuan's star coloring proves the `k = 5` path lower bound for every `n ≥ 5`. -/
theorem antiRamseyNum_pathGraph_five_ge (n : ℕ) (hn : 5 ≤ n) :
    n ≤ antiRamseyNum (pathGraph 5) n := by
  have hne : n ≠ 0 := by omega
  exact @antiRamseyNum_pathGraph_five_ge_aux n ⟨hne⟩ hn

end ErdosProblems.AntiRamseyPathFive

namespace ErdosProblems.AntiRamseyPathFiveExact

open SimpleGraph
set_option linter.style.haveILetI false

/-- Every admissible `P₅` coloring on at least five vertices uses at most
`n` colors. -/
theorem admissible_path_five_color_count_le (n q : ℕ) (hn : 5 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) : q ≤ n := by
  classical
  let G : SimpleGraph (Fin n) :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph χ hχ
  have hfree : (pathGraph 5).Free G :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph_free
      (pathGraph 5) χ hχ hno
  have hcard : G.edgeFinset.card = q :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph_card_edgeFinset χ hχ
  have hnat : Nat.card G.edgeSet = q := by
    rw [Nat.card_eq_fintype_card]
    rw [G.card_edgeSet]
    exact hcard
  by_contra hnot
  have hmore :
      n < (@SimpleGraph.edgeFinset (Fin n) G (SimpleGraph.fintypeEdgeSet G)).card := by
    have hc :
        (@SimpleGraph.edgeFinset (Fin n) G (SimpleGraph.fintypeEdgeSet G)).card =
          Nat.card G.edgeSet := by
      letI : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
      rw [Nat.card_eq_fintype_card]
      exact (G.card_edgeSet).symm
    omega
  obtain ⟨C, hfour, hfive⟩ :=
    ErdosProblems.AntiRamseyPathFiveComponents.exists_dense_four_component
      hn G hfree hmore
  obtain ⟨u, hu, h02, h03, h12, h13, h23⟩ :=
    ErdosProblems.AntiRamseyPathFiveDiamond.dense_component_has_diamond
      G C hfour hfive
  have hdiamond : ErdosProblems.AntiRamseyPathFiveTransfer.DiamondOn G
      (u 0) (u 1) (u 2) (u 3) := ⟨h02, h03, h12, h13, h23⟩
  exact (ErdosProblems.AntiRamseyPathFiveTransfer.no_representative_diamond_of_no_rainbow_path_five
    hn χ hχ hno u hu) hdiamond

/-- The `P₅` anti-Ramsey number is at most `n` for every `n ≥ 5`. -/
theorem antiRamseyNum_pathGraph_five_le (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n ≤ n := by
  classical
  let S : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
        ¬IsRainbow f.toHom χ}
  have hB : BddAbove S := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  change sSup S ≤ n
  refine (csSup_le_iff' hB).2 ?_
  intro q hq
  obtain ⟨χ, hχ, hno⟩ := hq
  exact admissible_path_five_color_count_le n q hn χ hχ hno

/-- The exact five-vertex path answer at every original-domain `n`. -/
theorem antiRamseyNum_pathGraph_five_eq (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n = n := by
  exact Nat.le_antisymm (antiRamseyNum_pathGraph_five_le n hn)
    (ErdosProblems.AntiRamseyPathFive.antiRamseyNum_pathGraph_five_ge n hn)

/-- The literal right-hand side of `erdos_1105.parts.ii` simplifies to `n`
when `k = 5` and `n ≥ 5`. -/
theorem path_five_formal_rhs_eq (n : ℕ) (hn : 5 ≤ n) :
    max ((5 - 2 : ℕ).choose 2 + 1)
      (((((5 - 1 : ℕ) / 2) - 1).choose 2) +
        (((5 - 1 : ℕ) / 2) - 1) * (n - ((5 - 1 : ℕ) / 2) + 1) +
          (if Odd (5 : ℕ) then 1 else 2)) = n := by
  norm_num
  omega

/-- The `k = 5` instance of the pinned Formal Conjectures path formula. -/
theorem path_five_formal_slice (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n =
      max ((5 - 2 : ℕ).choose 2 + 1)
        (((((5 - 1 : ℕ) / 2) - 1).choose 2) +
          (((5 - 1 : ℕ) / 2) - 1) * (n - ((5 - 1 : ℕ) / 2) + 1) +
            (if Odd (5 : ℕ) then 1 else 2)) := by
  rw [antiRamseyNum_pathGraph_five_eq n hn, path_five_formal_rhs_eq n hn]

end ErdosProblems.AntiRamseyPathFiveExact

namespace ErdosProblems.PathSetLower

/-- The first `t` vertices, truncated at `n`. -/
def hostVertices (t n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => v.val < t)

/-- Complete-graph edges meeting at least one of the first `t` vertices. -/
def incidentEdgeFinset (t n : ℕ) :
    Finset ((⊤ : SimpleGraph (Fin n)).edgeSet) :=
  Finset.univ.filter (fun e =>
    ∃ v ∈ (e.1 : Sym2 (Fin n)).toFinset, v ∈ hostVertices t n)

@[simp]
theorem mem_incidentEdgeFinset (t n : ℕ)
    (e : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    e ∈ incidentEdgeFinset t n ↔
      ∃ v ∈ (e.1 : Sym2 (Fin n)).toFinset, v.val < t := by
  simp [incidentEdgeFinset, hostVertices]

@[simp]
theorem mem_incidentEdgeFinset_mk (t n : ℕ) (u v : Fin n)
    (h : s(u, v) ∈ (⊤ : SimpleGraph (Fin n)).edgeSet) :
    (⟨s(u, v), h⟩ : (⊤ : SimpleGraph (Fin n)).edgeSet) ∈ incidentEdgeFinset t n ↔
      u.val < t ∨ v.val < t := by
  simp [mem_incidentEdgeFinset, Sym2.toFinset_mk_eq]

theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + a * b + b.choose 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_add, Nat.choose_succ_succ' (a + b) 1,
        Nat.choose_succ_succ' a 1, ih]
      simp only [Nat.reduceAdd, Nat.choose_one_right, Nat.succ_mul]
      omega

/-- The incident-edge palette has `t.choose 2 + t * (n - t)` colors. -/
theorem incidentEdgeFinset_card (t n : ℕ) (h : t ≤ n) :
    (incidentEdgeFinset t n).card = t.choose 2 + t * (n - t) := by
  classical
  let S : Finset (Fin n) := hostVertices t n
  have hS : S.card = t := by
    simpa [S, hostVertices, Nat.min_eq_right h] using
      (Fin.card_filter_val_lt (n := n) (m := t))
  have hSc : Sᶜ.card = n - t := by
    rw [Finset.card_compl, Fintype.card_fin, hS]
  let E : Finset (Sym2 (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset
  let P : Sym2 (Fin n) → Prop := fun e => ∃ v ∈ e.toFinset, v ∈ S
  have hMap : (incidentEdgeFinset t n).image Subtype.val = E.filter P := by
    ext e
    simp [incidentEdgeFinset, E, P, S, hostVertices, and_comm]
  have hInc : (incidentEdgeFinset t n).card = (E.filter P).card := by
    rw [← hMap, Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hAvoid : (E.filter (fun e => ¬ P e)).card = (n - t).choose 2 := by
    have hEq : E.filter (fun e => ¬ P e) =
        E.filter (fun e => e.toFinset ⊆ Sᶜ) := by
      ext e
      simp [P, Finset.subset_iff]
    rw [hEq]
    have hOffDiag : E.filter (fun e => e.toFinset ⊆ Sᶜ) =
        Sᶜ.offDiag.image Sym2.mk.uncurry := by
      calc
        E.filter (fun e => e.toFinset ⊆ Sᶜ) = E ∩ Sᶜ.sym2 := by
          simpa [E] using
            (SimpleGraph.filter_edgeFinset_toFinset_subset
              (G := (⊤ : SimpleGraph (Fin n))) (s := Sᶜ))
        _ = Sᶜ.sym2.filter (fun e => ¬ e.IsDiag) := by
          ext e
          simp [E, SimpleGraph.edgeFinset_top, and_comm]
        _ = Sᶜ.offDiag.image Sym2.mk.uncurry := by
          rw [Finset.sym2_eq_image, Sym2.filter_image_mk_not_isDiag]
    rw [hOffDiag, Sym2.card_image_offDiag, hSc]
  have hTotal : E.card = n.choose 2 := by
    simpa [E] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  have hPartition : (E.filter P).card + (E.filter (fun e => ¬ P e)).card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) P
  rw [hInc]
  have hN : n = t + (n - t) := by omega
  have hChoose : n.choose 2 = t.choose 2 + t * (n - t) + (n - t).choose 2 := by
    calc
      n.choose 2 = (t + (n - t)).choose 2 := congrArg (·.choose 2) hN
      _ = t.choose 2 + t * (n - t) + (n - t).choose 2 := choose_two_add _ _
  rw [hAvoid, hTotal, hChoose] at hPartition
  omega

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

/-- Indices of consecutive edges with at least one endpoint in `S`. -/
def pathTouched (m : ℕ) (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => i.castSucc ∈ S ∨ i.succ ∈ S)

/-- Indices of consecutive edges with both endpoints outside `S`. -/
def pathAvoiding (m : ℕ) (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ¬ (i.castSucc ∈ S ∨ i.succ ∈ S))

/-- At most two path edges touch each selected vertex. -/
theorem pathTouched_card_le (m : ℕ) (S : Finset (Fin (m + 1))) :
    (pathTouched m S).card ≤ 2 * S.card := by
  classical
  let L : Finset (Fin m) := Finset.univ.filter (fun i => i.castSucc ∈ S)
  let R : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ S)
  have hL : L.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (f := Fin.castSucc)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact (Fin.castSucc_injective m).injOn
  have hR : R.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (f := Fin.succ)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · exact (Fin.succ_injective m).injOn
  have hEq : pathTouched m S = L ∪ R := by
    ext i
    simp [pathTouched, L, R]
  calc
    (pathTouched m S).card = (L ∪ R).card := by rw [hEq]
    _ ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ S.card + S.card := Nat.add_le_add hL hR
    _ = 2 * S.card := by omega

/-- More than `ε` path edges avoid `S` once `S` is small enough. -/
theorem pathAvoiding_card_gt (m t ε : ℕ) (S : Finset (Fin (m + 1)))
    (hS : S.card ≤ t) (hm : 2 * t + ε < m) :
    ε < (pathAvoiding m S).card := by
  classical
  have hsum : (pathTouched m S).card + (pathAvoiding m S).card = m := by
    simpa [pathTouched, pathAvoiding] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i : Fin m => i.castSucc ∈ S ∨ i.succ ∈ S))
  have htouch := pathTouched_card_le m S
  omega

/-- Any coloring of the avoiding edges with only `ε` labels repeats a color. -/
theorem pathAvoiding_repeated_color (m t ε : ℕ) (S : Finset (Fin (m + 1)))
    (c : Fin m → Fin ε) (hS : S.card ≤ t) (hm : 2 * t + ε < m) :
    ∃ i ∈ pathAvoiding m S, ∃ j ∈ pathAvoiding m S,
      i ≠ j ∧ c i = c j := by
  classical
  have hcard := pathAvoiding_card_gt m t ε S hS hm
  by_contra hn
  have hinj : Set.InjOn c (pathAvoiding m S : Set (Fin m)) := by
    intro i hi j hj hij
    by_contra hne
    exact hn ⟨i, hi, j, hj, hne, hij⟩
  have hbound : (pathAvoiding m S).card ≤ ε := by
    have hmap : Set.MapsTo c (pathAvoiding m S : Finset (Fin m))
        (Finset.univ : Finset (Fin ε)) := by
      intro i hi
      exact Finset.mem_univ _
    have h := Finset.card_le_card_of_injOn c
      hmap hinj
    simpa using h
  omega

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

open SimpleGraph

def pathEdge (m : ℕ) (i : Fin m) : (pathGraph (m + 1)).edgeSet :=
  ⟨s(i.castSucc, i.succ), by
    rw [mem_edgeSet]
    apply pathGraph_adj.mpr
    left
    simp⟩

theorem pathEdge_injective (m : ℕ) : Function.Injective (pathEdge m) := by
  intro i j he
  have hs := congrArg Subtype.val he
  change s(i.castSucc, i.succ) = s(j.castSucc, j.succ) at hs
  rcases Sym2.eq_iff.mp hs with h | h
  · apply Fin.ext
    have hv := congrArg Fin.val h.1
    simpa using hv
  · have hv₁ := congrArg Fin.val h.1
    have hv₂ := congrArg Fin.val h.2
    simp at hv₁ hv₂
    omega

/-- A copied path cannot be rainbow when all edges away from a prefix of
`t` host vertices have colors in one palette of size `ε`, with
`2t + ε < m` where `m` is the number of path edges. -/
theorem noRainbowPath_of_smallOutsidePalette {m n t ε : ℕ} {C : Type*}
    (hε : 0 < ε) (hgap : 2 * t + ε < m)
    (χ : TopEdgeLabeling (Fin n) C) (palette : Fin ε → C)
    (hχ : ∀ a b : Fin n, (hab : a ≠ b) →
      t ≤ a.val → t ≤ b.val →
      ∃ z : Fin ε, χ.get a b ((top_adj a b).2 hab) = palette z) :
    ∀ f : (pathGraph (m + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
  classical
  intro f hrainbow
  change Function.Injective (EdgeLabeling.pullback χ f.toHom) at hrainbow
  let S : Finset (Fin (m + 1)) :=
    Finset.univ.filter (fun v => (f v).val < t)
  have hS : S.card ≤ t := by
    let g : S → Fin t := fun v =>
      ⟨(f v.1).val, (Finset.mem_filter.mp v.2).2⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply f.injective
      apply Fin.ext
      change (⟨(f a.1).val, _⟩ : Fin t) = ⟨(f b.1).val, _⟩ at hab
      exact congrArg (fun x : Fin t => x.val) hab
    simpa using Fintype.card_le_of_injective g hg
  have hcolor (i : Fin m) (hi : i ∈ pathAvoiding m S) :
      ∃ z : Fin ε,
        (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) = palette z := by
    have hav : ¬ (i.castSucc ∈ S ∨ i.succ ∈ S) := by
      exact (Finset.mem_filter.mp
        (show i ∈ Finset.univ.filter
          (fun q : Fin m => ¬ (q.castSucc ∈ S ∨ q.succ ∈ S)) from hi)).2
    have hl : t ≤ (f i.castSucc).val := by
      have hn : ¬ (f i.castSucc).val < t := by
        intro hlt
        exact hav (Or.inl (by simp [S, hlt]))
      omega
    have hr : t ≤ (f i.succ).val := by
      have hn : ¬ (f i.succ).val < t := by
        intro hlt
        exact hav (Or.inr (by simp [S, hlt]))
      omega
    have hne : f i.castSucc ≠ f i.succ := by
      apply f.injective.ne
      intro he
      have hv := congrArg Fin.val he
      simp at hv
    obtain ⟨z, hz⟩ := hχ (f i.castSucc) (f i.succ) hne hl hr
    refine ⟨z, ?_⟩
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathEdge] using hz
  let color (i : Fin m) : Fin ε :=
    if hi : i ∈ pathAvoiding m S then Classical.choose (hcolor i hi)
    else ⟨0, hε⟩
  have hcolor_eq (i : Fin m) (hi : i ∈ pathAvoiding m S) :
      (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) = palette (color i) := by
    dsimp [color]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hcolor i hi)
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    pathAvoiding_repeated_color m t ε S color hS hgap
  have hpull :
      (EdgeLabeling.pullback χ f.toHom) (pathEdge m i) =
        (EdgeLabeling.pullback χ f.toHom) (pathEdge m j) := by
    rw [hcolor_eq i hi, hcolor_eq j hj, heq]
  exact hij ((pathEdge_injective m) (hrainbow hpull))

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

/-- Size of the distinguished set in the second path lower coloring. -/
def fixedSetSize (k : ℕ) : ℕ := (k - 1) / 2 - 1

/-- Number of fresh colors on edges outside the distinguished set. -/
def outsidePaletteSize (k : ℕ) : ℕ := if Odd k then 1 else 2

theorem outsidePaletteSize_pos (k : ℕ) : 0 < outsidePaletteSize k := by
  by_cases ho : Odd k <;> simp [outsidePaletteSize, ho]

theorem outsidePaletteSize_le_two (k : ℕ) : outsidePaletteSize k ≤ 2 := by
  by_cases ho : Odd k <;> simp [outsidePaletteSize, ho]

/-- The path has more outside-only edges than fresh outside colors. -/
theorem fixedSetSize_gap (k : ℕ) (hk : 5 ≤ k) :
    2 * fixedSetSize k + outsidePaletteSize k < k - 1 := by
  by_cases ho : Odd k
  · simp only [outsidePaletteSize, ite_eq_left ho, fixedSetSize]
    obtain ⟨u, hu⟩ := ho
    omega
  · obtain ⟨u, hu⟩ := Nat.not_odd_iff_even.mp ho
    simp only [outsidePaletteSize, ite_eq_right ho, fixedSetSize]
    omega

/-- There are at least three host vertices away from the distinguished set. -/
theorem fixedSetSize_three_outside {k n : ℕ} (hk : 5 ≤ k) (hkn : k ≤ n) :
    fixedSetSize k + 3 ≤ n := by
  have ht : 1 ≤ fixedSetSize k := by
    simp only [fixedSetSize]
    omega
  have hε : 1 ≤ outsidePaletteSize k := outsidePaletteSize_pos k
  have hgap := fixedSetSize_gap k hk
  omega

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

/-- Give one distinguished edge color one when there are two palette labels;
give all other edges color zero. With one palette label every edge is zero. -/
noncomputable def twoPaletteColor {E : Type*} [DecidableEq E] {ε : ℕ}
    (hε : 0 < ε) (e₁ : E) : E → Fin ε :=
  fun e =>
    if h₂ : ε = 2 then
      if e = e₁ then Fin.cast h₂.symm (1 : Fin 2)
      else Fin.cast h₂.symm (0 : Fin 2)
    else ⟨0, hε⟩

/-- Two different available edges realize every label in a palette of size
one or two. -/
theorem twoPaletteColor_surjective_on_pair {E : Type*} [DecidableEq E]
    {ε : ℕ} (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : E) (hne : e₀ ≠ e₁) :
    ∀ z : Fin ε, ∃ e : E, (e = e₀ ∨ e = e₁) ∧
      twoPaletteColor hε e₁ e = z := by
  intro z
  by_cases h₂ : ε = 2
  · subst ε
    fin_cases z
    · refine ⟨e₀, Or.inl rfl, ?_⟩
      simp [twoPaletteColor, hne]
    · refine ⟨e₁, Or.inr rfl, ?_⟩
      simp [twoPaletteColor]
  · have h₁ : ε = 1 := by omega
    subst ε
    fin_cases z
    exact ⟨e₀, Or.inl rfl, by simp [twoPaletteColor]⟩

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

open SimpleGraph

def completeEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  ⟨s(u, v), (top_adj u v).2 huv⟩

theorem completeEdge_not_incident {t n : ℕ}
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    completeEdge u v huv ∉ incidentEdgeFinset t n := by
  intro hmem
  have hval : u.val < t ∨ v.val < t :=
    (mem_incidentEdgeFinset_mk t n u v ((top_adj u v).2 huv)).mp hmem
  omega

def hostAt {t n : ℕ} (h : t + 3 ≤ n) (i : Fin 3) : Fin n :=
  ⟨t + i.val, by omega⟩

/-- An outside edge that receives color zero. -/
def outsideZeroEdge {t n : ℕ} (h : t + 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  completeEdge (hostAt h 0) (hostAt h 2) (by
    intro he
    have hv := congrArg Fin.val he
    simp [hostAt] at hv)

/-- A distinct outside edge that receives color one if there are two labels. -/
def outsideOneEdge {t n : ℕ} (h : t + 3 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).edgeSet :=
  completeEdge (hostAt h 0) (hostAt h 1) (by
    intro he
    have hv := congrArg Fin.val he
    simp [hostAt] at hv)

theorem outsideZeroEdge_not_incident {t n : ℕ} (h : t + 3 ≤ n) :
    outsideZeroEdge h ∉ incidentEdgeFinset t n := by
  apply completeEdge_not_incident
  · simp [hostAt]
  · simp [hostAt]

theorem outsideOneEdge_not_incident {t n : ℕ} (h : t + 3 ≤ n) :
    outsideOneEdge h ∉ incidentEdgeFinset t n := by
  apply completeEdge_not_incident
  · simp [hostAt]
  · simp [hostAt]

theorem outsideEdges_ne {t n : ℕ} (h : t + 3 ≤ n) :
    outsideZeroEdge h ≠ outsideOneEdge h := by
  intro he
  have hs := congrArg Subtype.val he
  change s(hostAt h 0, hostAt h 2) = s(hostAt h 0, hostAt h 1) at hs
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · have hv := congrArg Fin.val hsame.2
    simp [hostAt] at hv
  · have hv := congrArg Fin.val hswap.1
    simp [hostAt] at hv

abbrev RawSetColors (t n ε : ℕ) : Type :=
  (incidentEdgeFinset t n) ⊕ Fin ε

noncomputable def rawSetColor {t n ε : ℕ} (hε : 0 < ε)
    (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    TopEdgeLabeling (Fin n) (RawSetColors t n ε) := by
  classical
  exact fun e =>
    if he : e ∈ incidentEdgeFinset t n then
      Sum.inl ⟨e, he⟩
    else Sum.inr (twoPaletteColor hε e₁ e)

theorem rawSetColor_surjective {t n ε : ℕ}
    (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h₀ : e₀ ∉ incidentEdgeFinset t n)
    (h₁ : e₁ ∉ incidentEdgeFinset t n)
    (hne : e₀ ≠ e₁) :
    Function.Surjective (rawSetColor (t := t) hε e₁) := by
  classical
  intro z
  cases z with
  | inl e =>
      refine ⟨e.1, ?_⟩
      simp [rawSetColor, e.2]
  | inr q =>
      obtain ⟨e, he, hq⟩ :=
        twoPaletteColor_surjective_on_pair hε hε₂ e₀ e₁ hne q
      refine ⟨e, ?_⟩
      rcases he with rfl | rfl
      · simp [rawSetColor, h₀, hq]
      · simp [rawSetColor, h₁, hq]

theorem rawSetColors_card (t n ε : ℕ) (h : t ≤ n) :
    Fintype.card (RawSetColors t n ε) =
      t.choose 2 + t * (n - t) + ε := by
  classical
  change Fintype.card ((incidentEdgeFinset t n) ⊕ Fin ε) =
    t.choose 2 + t * (n - t) + ε
  rw [Fintype.card_sum, Fintype.card_coe (incidentEdgeFinset t n),
    Fintype.card_fin, incidentEdgeFinset_card t n h]

theorem rawSetColor_get_outside {t n ε : ℕ}
    (hε : 0 < ε) (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    (rawSetColor (t := t) hε e₁).get u v ((top_adj u v).2 huv) =
      Sum.inr (twoPaletteColor hε e₁ (completeEdge u v huv)) := by
  have hnot := completeEdge_not_incident u v huv hu hv
  change (rawSetColor (t := t) hε e₁) (completeEdge u v huv) =
    Sum.inr (twoPaletteColor hε e₁ (completeEdge u v huv))
  simp only [rawSetColor, dite_eq_right hnot]

noncomputable def setColor {t n ε : ℕ} (h : t ≤ n) (hε : 0 < ε)
    (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet) :
    TopEdgeLabeling (Fin n) (Fin (t.choose 2 + t * (n - t) + ε)) :=
  fun e => Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (rawSetColor (t := t) hε e₁ e))

theorem setColor_surjective {t n ε : ℕ} (h : t ≤ n)
    (hε : 0 < ε) (hε₂ : ε ≤ 2)
    (e₀ e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (h₀ : e₀ ∉ incidentEdgeFinset t n)
    (h₁ : e₁ ∉ incidentEdgeFinset t n)
    (hne : e₀ ≠ e₁) :
    Function.Surjective (setColor h hε e₁) := by
  classical
  intro z
  let d : RawSetColors t n ε :=
    (Fintype.equivFin (RawSetColors t n ε)).symm
      (Fin.cast (rawSetColors_card t n ε h).symm z)
  obtain ⟨e, he⟩ := rawSetColor_surjective (t := t) hε hε₂ e₀ e₁ h₀ h₁ hne d
  refine ⟨e, ?_⟩
  change Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (rawSetColor (t := t) hε e₁ e)) = z
  rw [he]
  simp [d]

/-- The exact fresh palette inside the relabeled `Fin` color type. -/
noncomputable def freshSetColor {t n ε : ℕ} (h : t ≤ n) (z : Fin ε) :
    Fin (t.choose 2 + t * (n - t) + ε) :=
  Fin.cast (rawSetColors_card t n ε h)
    ((Fintype.equivFin (RawSetColors t n ε)) (Sum.inr z))

theorem setColor_get_outside {t n ε : ℕ} (h : t ≤ n)
    (hε : 0 < ε) (e₁ : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (u v : Fin n) (huv : u ≠ v)
    (hu : t ≤ u.val) (hv : t ≤ v.val) :
    (setColor h hε e₁).get u v ((top_adj u v).2 huv) =
      freshSetColor h (twoPaletteColor hε e₁ (completeEdge u v huv)) := by
  have hraw := rawSetColor_get_outside hε e₁ u v huv hu hv
  simpa [setColor, freshSetColor, EdgeLabeling.get] using
    congrArg (fun c : RawSetColors t n ε =>
      Fin.cast (rawSetColors_card t n ε h)
        ((Fintype.equivFin (RawSetColors t n ε)) c)) hraw

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

open SimpleGraph

def admissiblePathCounts (k n : ℕ) : Set ℕ :=
  {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
    ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}

theorem admissiblePathCounts_bddAbove (k n : ℕ) :
    BddAbove (admissiblePathCounts k n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro q hq
  obtain ⟨χ, hsurj, _⟩ := hq
  simpa using Fintype.card_le_of_surjective χ hsurj

/-- Yuan's `(ℓ - 1)`-hub construction gives its exact color count as a lower
bound on `antiRamseyNum (pathGraph k) n` for every `n ≥ k ≥ 5`. -/
theorem pathSetLower (k n : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    (fixedSetSize k).choose 2 +
      fixedSetSize k * (n - fixedSetSize k) + outsidePaletteSize k
        ≤ antiRamseyNum (pathGraph k) n := by
  let t := fixedSetSize k
  let ε := outsidePaletteSize k
  change t.choose 2 + t * (n - t) + ε ≤ antiRamseyNum (pathGraph k) n
  have hε : 0 < ε := outsidePaletteSize_pos k
  have hε₂ : ε ≤ 2 := outsidePaletteSize_le_two k
  have hgap : 2 * t + ε < k - 1 := fixedSetSize_gap k hk
  have hthree : t + 3 ≤ n := fixedSetSize_three_outside hk hkn
  have ht : t ≤ n := by omega
  let e₀ := outsideZeroEdge hthree
  let e₁ := outsideOneEdge hthree
  have h₀ : e₀ ∉ incidentEdgeFinset t n := outsideZeroEdge_not_incident hthree
  have h₁ : e₁ ∉ incidentEdgeFinset t n := outsideOneEdge_not_incident hthree
  have hne : e₀ ≠ e₁ := outsideEdges_ne hthree
  let χ := setColor ht hε e₁
  have hsurj : Function.Surjective χ :=
    setColor_surjective ht hε hε₂ e₀ e₁ h₀ h₁ hne
  have hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
    have hpalette :
        ∀ a b : Fin n, (hab : a ≠ b) →
          t ≤ a.val → t ≤ b.val →
          ∃ z : Fin ε,
            χ.get a b ((top_adj a b).2 hab) = freshSetColor ht z := by
      intro a b hab ha hb
      refine ⟨twoPaletteColor hε e₁ (completeEdge a b hab), ?_⟩
      simpa [χ] using setColor_get_outside ht hε e₁ a b hab ha hb
    have hcopy :=
      noRainbowPath_of_smallOutsidePalette
        (m := k - 1) (n := n) (t := t) (ε := ε)
        hε hgap χ (freshSetColor ht) hpalette
    have hkEq : k - 1 + 1 = k := by omega
    rw [hkEq] at hcopy
    exact hcopy
  change t.choose 2 + t * (n - t) + ε ≤ sSup (admissiblePathCounts k n)
  apply le_csSup (admissiblePathCounts_bddAbove k n)
  exact ⟨χ, hsurj, hno⟩

/-- The same lower bound in the literal second-term notation of Formal
Conjectures #1105, part ii. -/
theorem secondTerm_lower (k n : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    (ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε
      ≤ antiRamseyNum (pathGraph k) n := by
  dsimp
  have hℓ : 1 ≤ (k - 1) / 2 := by omega
  have hℓn : (k - 1) / 2 ≤ n := by omega
  have hsub : n - ((k - 1) / 2 - 1) = n - (k - 1) / 2 + 1 := by omega
  have hres := pathSetLower k n hk hkn
  change ((k - 1) / 2 - 1).choose 2 +
    ((k - 1) / 2 - 1) * (n - ((k - 1) / 2 - 1)) +
    (if Odd k then 1 else 2) ≤ antiRamseyNum (pathGraph k) n at hres
  rw [hsub] at hres
  exact hres

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSetLower

open SimpleGraph

/-- Both terms of the proposed exact path formula are lower bounds in the
original range `n ≥ k ≥ 5`. -/
theorem pathMaxLower (k n : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    max ((k - 2).choose 2 + 1)
      ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)
        ≤ antiRamseyNum (pathGraph k) n := by
  dsimp
  exact max_le
    (ErdosProblems.PathCliqueLower.pathCliqueLower hk hkn)
    (secondTerm_lower k n hk hkn)

end ErdosProblems.PathSetLower

namespace ErdosProblems.PathSelectedC6FourthLeaf

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Cycle hubs are positions0,2,4; its leaves1,3,5. Vertex6 is fully
spoked to the hubs, and vertex7 is unrestricted. Additional edges are allowed. -/
structure RepresentativeC6FourthLeafOn {V : Type*}
    (G : SimpleGraph V) (u : Fin 8 → V) : Prop where
  c01 : G.Adj (u 0) (u 1)
  c12 : G.Adj (u 1) (u 2)
  c23 : G.Adj (u 2) (u 3)
  c34 : G.Adj (u 3) (u 4)
  c45 : G.Adj (u 4) (u 5)
  c50 : G.Adj (u 5) (u 0)
  y0 : G.Adj (u 6) (u 0)
  y2 : G.Adj (u 6) (u 2)
  y4 : G.Adj (u 6) (u 4)

def motifEdgeIndex (i : Fin 9) : Sym2 (Fin 8) :=
  if i = 0 then s(0, 1)
  else if i = 1 then s(1, 2)
  else if i = 2 then s(2, 3)
  else if i = 3 then s(3, 4)
  else if i = 4 then s(4, 5)
  else if i = 5 then s(5, 0)
  else if i = 6 then s(6, 0)
  else if i = 7 then s(6, 2)
  else s(6, 4)

theorem motifEdgeIndex_injective : Function.Injective motifEdgeIndex := by
  decide

theorem motifEdge_mem {V : Type*}
    (G : SimpleGraph V) (u : Fin 8 → V)
    (h : RepresentativeC6FourthLeafOn G u) (i : Fin 9) :
    Sym2.map u (motifEdgeIndex i) ∈ G.edgeSet := by
  fin_cases i
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c01
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c12
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c23
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c34
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c45
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.c50
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y0
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y2
  · simpa [motifEdgeIndex, Sym2.map_mk] using h.y4

/-- The six selected-edge rows are
[6,5,4,3,2,1], [7,2,3,4,5,0], [7,1,0,5,4,3],
[8,4,5,0,1,2], [8,3,2,1,0,5], [6,0,1,2,3,4]. -/
def chosenEdgeIndex (r : Fin 6) (i : Fin 6) : Fin 9 :=
  if r = 0 then
    if i = 0 then 6 else if i = 1 then 5 else if i = 2 then 4
    else if i = 3 then 3 else if i = 4 then 2 else 1
  else if r = 1 then
    if i = 0 then 7 else if i = 1 then 2 else if i = 2 then 3
    else if i = 3 then 4 else if i = 4 then 5 else 0
  else if r = 2 then
    if i = 0 then 7 else if i = 1 then 1 else if i = 2 then 0
    else if i = 3 then 5 else if i = 4 then 4 else 3
  else if r = 3 then
    if i = 0 then 8 else if i = 1 then 4 else if i = 2 then 5
    else if i = 3 then 0 else if i = 4 then 1 else 2
  else if r = 4 then
    if i = 0 then 8 else if i = 1 then 3 else if i = 2 then 2
    else if i = 3 then 1 else if i = 4 then 0 else 5
  else
    if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 1
    else if i = 3 then 2 else if i = 4 then 3 else 4

theorem choose_avoids {E : Type*}
    (d : Fin 9 → E) (hd : Function.Injective d) (old : E)
    (j : Fin 9) (hj : old = d j) (r : Fin 6)
    (hr : ∀ i, j ≠ chosenEdgeIndex r i) :
    ∀ i, old ≠ d (chosenEdgeIndex r i) := by
  intro i
  rw [hj]
  exact hd.ne (hr i)

/-- All six cycle-owner cases and all three y-spoke cases, plus every owner
outside those nine actual selected edges. No owner premise is supplied. -/
theorem avoid_one {E : Type*}
    (d : Fin 9 → E) (hd : Function.Injective d) (old : E) :
    ∃ row : Fin 6, ∀ i : Fin 6, old ≠ d (chosenEdgeIndex row i) := by
  classical
  by_cases h0 : old = d 0
  · exact ⟨0, choose_avoids d hd old 0 h0 0 (by decide)⟩
  by_cases h1 : old = d 1
  · exact ⟨1, choose_avoids d hd old 1 h1 1 (by decide)⟩
  by_cases h2 : old = d 2
  · exact ⟨2, choose_avoids d hd old 2 h2 2 (by decide)⟩
  by_cases h3 : old = d 3
  · exact ⟨3, choose_avoids d hd old 3 h3 3 (by decide)⟩
  by_cases h4 : old = d 4
  · exact ⟨4, choose_avoids d hd old 4 h4 4 (by decide)⟩
  by_cases h5 : old = d 5
  · exact ⟨5, choose_avoids d hd old 5 h5 5 (by decide)⟩
  by_cases h6 : old = d 6
  · exact ⟨1, choose_avoids d hd old 6 h6 1 (by decide)⟩
  by_cases h7 : old = d 7
  · exact ⟨0, choose_avoids d hd old 7 h7 0 (by decide)⟩
  by_cases h8 : old = d 8
  · exact ⟨0, choose_avoids d hd old 8 h8 0 (by decide)⟩
  refine ⟨0, ?_⟩
  intro i
  fin_cases i <;> simp_all [chosenEdgeIndex]

/-- Every order starts at w7,y6 and opens the same selected C6 at the
cycle edge whose index is row. Its first cycle vertex is a hub. -/
def openOrderIndex (r : Fin 6) (i : Fin 8) : Fin 8 :=
  if i = 0 then 7
  else if i = 1 then 6
  else if r = 0 then
    if i = 2 then 0 else if i = 3 then 5 else if i = 4 then 4
    else if i = 5 then 3 else if i = 6 then 2 else 1
  else if r = 1 then
    if i = 2 then 2 else if i = 3 then 3 else if i = 4 then 4
    else if i = 5 then 5 else if i = 6 then 0 else 1
  else if r = 2 then
    if i = 2 then 2 else if i = 3 then 1 else if i = 4 then 0
    else if i = 5 then 5 else if i = 6 then 4 else 3
  else if r = 3 then
    if i = 2 then 4 else if i = 3 then 5 else if i = 4 then 0
    else if i = 5 then 1 else if i = 6 then 2 else 3
  else if r = 4 then
    if i = 2 then 4 else if i = 3 then 3 else if i = 4 then 2
    else if i = 5 then 1 else if i = 6 then 0 else 5
  else
    if i = 2 then 0 else if i = 3 then 1 else if i = 4 then 2
    else if i = 5 then 3 else if i = 6 then 4 else 5

theorem openOrderIndex_injective (r : Fin 6) :
    Function.Injective (openOrderIndex r) := by
  fin_cases r <;> decide

/-- One exact owner-avoiding Copy bridge for the original coloring.
The motif has nine selected edges; no favorable representative is required. -/
theorem rainbow_path_eight_of_representative_c6_and_fourth_leaf {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (u : Fin 8 → Fin n) (hu : Function.Injective u)
    (h : RepresentativeC6FourthLeafOn (selectedGraph χ r) u) :
    ∃ f : (pathGraph 8).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let e : HostEdge n :=
    ⟨s(u 7, u 6),
      (SimpleGraph.mem_edgeSet (⊤ : SimpleGraph (Fin n))).mpr
        ((top_adj _ _).mpr (hu.ne (by decide)))⟩
  let old : Sym2 (Fin n) := (r.edge (χ e)).val
  let r' : RepresentativeChoice χ := r.replace e
  let L : SimpleGraph (Fin n) := selectedGraph χ r
  let L' : SimpleGraph (Fin n) := selectedGraph χ r'
  let d : Fin 9 → Sym2 (Fin n) := fun i => Sym2.map u (motifEdgeIndex i)
  have hd : Function.Injective d := by
    intro i j hij
    apply motifEdgeIndex_injective
    apply Sym2.map.injective hu
    simpa [d] using hij
  obtain ⟨row, hrow⟩ := avoid_one d hd old
  have hle : L.deleteEdges {old} ≤ L' := by
    simpa [L, L', r', old] using delete_selectedEdge_le_replace χ r e
  have hretained (i : Fin 9) (hne : old ≠ d i) : d i ∈ L'.edgeSet := by
    have he : d i ∈ L.edgeSet := by
      simpa [d, L] using motifEdge_mem L u h i
    have hed : d i ∈ (L.deleteEdges {old}).edgeSet := by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨he, by simpa using hne.symm⟩
    exact SimpleGraph.edgeSet_mono hle hed
  have hchord : L'.Adj (u 7) (u 6) := by
    have he := replacedEdge_mem χ r e
    simpa [L', r', e] using he
  let w : Fin 8 → Fin n := u ∘ openOrderIndex row
  have hw : Function.Injective w := hu.comp (openOrderIndex_injective row)
  have hmotifStep (i : Fin 6) :
      L'.Adj (w (Fin.succ (Fin.castSucc i))) (w (Fin.succ (Fin.succ i))) := by
    have hval :
        s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) =
          d (chosenEdgeIndex row i) := by
      fin_cases row <;> fin_cases i <;>
        simp [w, d, openOrderIndex, chosenEdgeIndex, motifEdgeIndex,
          Sym2.map_mk, Sym2.eq_swap]
    change s(w (Fin.succ (Fin.castSucc i)), w (Fin.succ (Fin.succ i))) ∈ L'.edgeSet
    rw [hval]
    exact hretained (chosenEdgeIndex row i) (hrow i)
  have hstep (i : Fin 7) : L'.Adj (w i.castSucc) (w i.succ) := by
    fin_cases i
    · simpa [w, openOrderIndex] using hchord
    · simpa using hmotifStep 0
    · simpa using hmotifStep 1
    · simpa using hmotifStep 2
    · simpa using hmotifStep 3
    · simpa using hmotifStep 4
    · simpa using hmotifStep 5
  let φ : (pathGraph 8) →g L' :=
    ⟨w, by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · have hi7 : i.val < 7 := by have hj8 := j.isLt; omega
        let t : Fin 7 := ⟨i.val, hi7⟩
        have hi : i = t.castSucc := Fin.ext rfl
        have hj : j = t.succ := Fin.ext hij.symm
        rw [hi, hj]
        exact hstep t
      · have hj7 : j.val < 7 := by have hi8 := i.isLt; omega
        let t : Fin 7 := ⟨j.val, hj7⟩
        have hj : j = t.castSucc := Fin.ext rfl
        have hi : i = t.succ := Fin.ext hji.symm
        rw [hi, hj]
        exact (hstep t).symm⟩
  let f : (pathGraph 8).Copy L' := ⟨φ, hw⟩
  refine ⟨(Copy.ofLE L' (⊤ : SimpleGraph (Fin n)) le_top).comp f, ?_⟩
  simpa [L', r'] using copy_in_selectedGraph_isRainbow χ (r.replace e) f

end ErdosProblems.PathSelectedC6FourthLeaf

namespace ErdosProblems.PathSelectedS3MotifExtractor

open SimpleGraph Finset
open ErdosProblems.PathSelectedC6FourthLeaf

theorem three_hub_card
    (H : SimpleGraph (Fin 8)) [DecidableRel H.Adj]
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    H.edgeFinset.card = 18 := by
  classical
  have houtside : (univ \ U).card = 5 := by
    rw [card_sdiff_of_subset (subset_univ U)]
    simp [hU]
  have hd : ∀ x : Fin 8, H.degree x = if x ∈ U then 7 else 3 := by
    intro x
    by_cases hx : x ∈ U
    · have hn : H.neighborFinset x = univ.erase x := by
        ext y
        simp only [H.mem_neighborFinset, mem_erase, mem_univ, and_true]
        rw [hH]
        simp [hx, ne_comm]
      rw [ite_eq_left hx, ← H.card_neighborFinset_eq_degree x, hn]
      simp
    · have hn : H.neighborFinset x = U := by
        ext y
        rw [H.mem_neighborFinset, hH]
        constructor
        · rintro ⟨_, hy | hy⟩
          · exact False.elim (hx hy)
          · exact hy
        · intro hy
          refine ⟨?_, Or.inr hy⟩
          intro hxy
          exact hx (hxy.symm ▸ hy)
      rw [ite_eq_right hx, ← H.card_neighborFinset_eq_degree x, hn, hU]
  have hfilter : univ.filter (fun x : Fin 8 => x ∈ U) = U := by
    ext x
    simp
  have hnotfilter : univ.filter (fun x : Fin 8 => x ∉ U) = univ \ U := by
    ext x
    simp
  have hsum : ∑ x : Fin 8, H.degree x = 36 := by
    simp_rw [hd]
    rw [Finset.sum_ite]
    simp [hfilter, hnotfilter, hU, houtside]
  have hhand := H.sum_degrees_eq_twice_card_edges
  omega

theorem four_fully_spoked_leaves
    (R H : SimpleGraph (Fin 8)) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hRH : R ≤ H) (hcard : 17 ≤ R.edgeFinset.card)
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    ∃ A : Finset (Fin 8), A.card = 4 ∧ A ⊆ univ \ U ∧
      ∀ x ∈ A, ∀ a ∈ U, R.Adj x a := by
  classical
  let L : Finset (Fin 8) := univ \ U
  let B : Finset (Fin 8) := L.filter (fun x => ∃ a ∈ U, ¬R.Adj x a)
  let M : Finset (Sym2 (Fin 8)) := H.edgeFinset \ R.edgeFinset
  have hL : L.card = 5 := by
    dsimp [L]
    rw [card_sdiff_of_subset (subset_univ U)]
    simp [hU]
  have hHcard := three_hub_card H U hU hH
  have hM : M.card ≤ 1 := by
    dsimp [M]
    rw [card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hRH)]
    omega
  have hb : ∀ x : B, ∃ a ∈ U, ¬R.Adj x.val a := by
    intro x
    exact (mem_filter.mp x.property).2
  let a : B → Fin 8 := fun x => Classical.choose (hb x)
  have ha (x : B) : a x ∈ U ∧ ¬R.Adj x.val (a x) :=
    Classical.choose_spec (hb x)
  have hxout (x : B) : x.val ∉ U := by
    exact (mem_sdiff.mp ((mem_filter.mp x.property).1)).2
  let f : B → M := fun x => ⟨s(x.val, a x), by
    apply mem_sdiff.mpr
    constructor
    · apply SimpleGraph.mem_edgeFinset.mpr
      apply (H.mem_edgeSet).mpr
      apply (hH x.val (a x)).mpr
      refine ⟨?_, Or.inr (ha x).1⟩
      intro heq
      exact hxout x (heq.symm ▸ (ha x).1)
    · intro he
      exact (ha x).2 ((R.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp he))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have he : s(x.val, a x) = s(y.val, a y) := congrArg Subtype.val hxy
    rcases Sym2.eq_iff.mp he with he | he
    · exact Subtype.ext he.1
    · exact False.elim (hxout x (he.1.symm ▸ (ha y).1))
  have hB : B.card ≤ 1 := by
    have hBM : B.card ≤ M.card := Finset.card_le_card_of_injective hf
    omega
  let G : Finset (Fin 8) := L \ B
  have hBG : B ⊆ L := filter_subset _ _
  have hG : 4 ≤ G.card := by
    dsimp [G]
    rw [card_sdiff_of_subset hBG]
    omega
  obtain ⟨A, hAG, hA⟩ := Finset.exists_subset_card_eq hG
  refine ⟨A, hA, ?_, ?_⟩
  · intro x hx
    exact (mem_sdiff.mp (hAG hx)).1
  · intro x hx b hbU
    have hxG := mem_sdiff.mp (hAG hx)
    by_contra hbad
    exact hxG.2 (mem_filter.mpr ⟨hxG.1, b, hbU, hbad⟩)

def weave (a : Fin 3 → Fin 8) (b : Fin 4 → Fin 8)
    (w : Fin 8) (i : Fin 8) : Fin 8 :=
  if i = 0 then a 0 else if i = 1 then b 0
  else if i = 2 then a 1 else if i = 3 then b 1
  else if i = 4 then a 2 else if i = 5 then b 2
  else if i = 6 then b 3 else w

theorem weave_injective
    (a : Fin 3 → Fin 8) (b : Fin 4 → Fin 8) (w : Fin 8)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j)
    (haw : ∀ i, a i ≠ w) (hbw : ∀ i, b i ≠ w) :
    Function.Injective (weave a b w) := by
  have hba : ∀ i j, b i ≠ a j := fun i j => (hab j i).symm
  have hwa : ∀ i, w ≠ a i := fun i => (haw i).symm
  have hwb : ∀ i, w ≠ b i := fun i => (hbw i).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [weave, ha.eq_iff, hb.eq_iff]

/-- Literal graph-only motif extraction. U consists of the three S3 hubs.
The selected subgraph may omit one host edge at any actual location. -/
theorem selected_c6_fourth_leaf_of_seventeen_edges_in_three_hub
    (R H : SimpleGraph (Fin 8)) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hRH : R ≤ H) (hcard : 17 ≤ R.edgeFinset.card)
    (U : Finset (Fin 8)) (hU : U.card = 3)
    (hH : ∀ x y, H.Adj x y ↔ x ≠ y ∧ (x ∈ U ∨ y ∈ U)) :
    ∃ u : Fin 8 → Fin 8, Function.Injective u ∧ RepresentativeC6FourthLeafOn R u := by
  classical
  obtain ⟨A, hA, hAL, hfull⟩ := four_fully_spoked_leaves R H hRH hcard U hU hH
  have hUA : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxA
    exact (mem_sdiff.mp (hAL hxA)).2 hxU
  have hseven : (U ∪ A).card = 7 := by
    rw [card_union_of_disjoint hUA, hU, hA]
  have hremaining : (univ \ (U ∪ A)).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ (U ∪ A))]
    simp [hseven]
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < (univ \ (U ∪ A)).card by omega)
  have hwU : w ∉ U := by
    intro hwU
    exact (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inl hwU))
  have hwA : w ∉ A := by
    intro hwA
    exact (mem_sdiff.mp hw).2 (mem_union.mpr (Or.inr hwA))
  let eU : U ≃ Fin 3 := Finset.equivFinOfCardEq hU
  let eA : A ≃ Fin 4 := Finset.equivFinOfCardEq hA
  let a : Fin 3 → Fin 8 := fun i => (eU.symm i).val
  let b : Fin 4 → Fin 8 := fun i => (eA.symm i).val
  have haU (i : Fin 3) : a i ∈ U := (eU.symm i).property
  have hbA (i : Fin 4) : b i ∈ A := (eA.symm i).property
  have hainj : Function.Injective a := by
    intro i j hij
    exact eU.symm.injective (Subtype.ext hij)
  have hbinj : Function.Injective b := by
    intro i j hij
    exact eA.symm.injective (Subtype.ext hij)
  have hab : ∀ i j, a i ≠ b j := by
    intro i j heq
    exact (mem_sdiff.mp (hAL (hbA j))).2 (heq ▸ haU i)
  have haw : ∀ i, a i ≠ w := by
    intro i heq
    exact hwU (heq ▸ haU i)
  have hbw : ∀ i, b i ≠ w := by
    intro i heq
    exact hwA (heq ▸ hbA i)
  have hadj (i : Fin 4) (j : Fin 3) : R.Adj (b i) (a j) :=
    hfull (b i) (hbA i) (a j) (haU j)
  refine ⟨weave a b w, weave_injective a b w hainj hbinj hab haw hbw, ?_⟩
  constructor
  · simpa [weave] using (hadj 0 0).symm
  · simpa [weave] using hadj 0 1
  · simpa [weave] using (hadj 1 1).symm
  · simpa [weave] using hadj 1 2
  · simpa [weave] using (hadj 2 2).symm
  · simpa [weave] using hadj 2 0
  · simpa [weave] using hadj 3 0
  · simpa [weave] using hadj 3 1
  · simpa [weave] using hadj 3 2

end ErdosProblems.PathSelectedS3MotifExtractor

namespace ErdosProblems.AntiRamseyPathSixTransfer

open ErdosProblems.AntiRamseyPathFiveUpper

variable {C : Type*}

/-- The first five of seven distinct selected colors belong to the rooted
diamond; the final two are the pendant edges. -/
def pathSixCoreColors (d : Fin 7 → C) : Fin 5 → C :=
  fun i => d ⟨i.val, by omega⟩

/-- Remove the pendant-edge position from a five-edge path. The two inputs
`0` and `1` deliberately share output `0`; injectivity is used only away
from input `1`. -/
def pathSixCompress (i : Fin 5) : Fin 4 :=
  if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 1
  else if i = 3 then 2 else 3

/-- `true` uses the first pendant color, and `false` the second. -/
def pathSixPendantIndex (s : Bool) : Fin 7 := if s then 5 else 6

/-- Five consecutive edge colors: outside-to-outside, pendant, then three
edges of a rooted diamond Hamiltonian path. -/
def pathSixChosenColors (d : Fin 7 → C) (z : C)
    (s : Bool) (r : Fin 4) (i : Fin 5) : C :=
  if i = 1 then d (pathSixPendantIndex s)
  else extendedPathColors (pathSixCoreColors d) z r (pathSixCompress i)

theorem pathSixCompress_injective_away_pendant :
    ∀ i j : Fin 5, i ≠ 1 → j ≠ 1 →
      pathSixCompress i = pathSixCompress j → i = j := by
  decide

theorem pathSixPendantIndex_ge_five (s : Bool) :
    5 ≤ (pathSixPendantIndex s).val := by
  cases s <;> decide

theorem pendant_color_ne_core (d : Fin 7 → C)
    (hd : Function.Injective d) (s : Bool) (j : Fin 5) :
    d (pathSixPendantIndex s) ≠ pathSixCoreColors d j := by
  intro he
  have hindex := congrArg Fin.val (hd he)
  have hbig := pathSixPendantIndex_ge_five s
  dsimp [pathSixCoreColors] at hindex
  omega

theorem pendant_color_ne_extended (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) (s : Bool) (r : Fin 4)
    (hz : d (pathSixPendantIndex s) ≠ z) (j : Fin 4) :
    d (pathSixPendantIndex s) ≠
      extendedPathColors (pathSixCoreColors d) z r j := by
  by_cases hj : j = 0
  · simpa [extendedPathColors, hj] using hz
  · simpa [extendedPathColors, hj] using
      pendant_color_ne_core d hd s (diamondPathEdgeIndex r j)

theorem pathSixChosenColors_injective (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) (s : Bool) (r : Fin 4)
    (hr : Function.Injective
      (extendedPathColors (pathSixCoreColors d) z r))
    (hz : d (pathSixPendantIndex s) ≠ z) :
    Function.Injective (pathSixChosenColors d z s r) := by
  intro i j hij
  by_cases hi : i = 1
  · subst i
    by_cases hj : j = 1
    · subst j
      rfl
    · have he : d (pathSixPendantIndex s) =
          extendedPathColors (pathSixCoreColors d) z r
            (pathSixCompress j) := by
        simpa [pathSixChosenColors, hj] using hij
      exact False.elim
        ((pendant_color_ne_extended d hd z s r hz (pathSixCompress j)) he)
  · by_cases hj : j = 1
    · subst j
      have he : extendedPathColors (pathSixCoreColors d) z r
          (pathSixCompress i) = d (pathSixPendantIndex s) := by
        simpa [pathSixChosenColors, hi] using hij
      exact False.elim
        ((pendant_color_ne_extended d hd z s r hz (pathSixCompress i)) he.symm)
    · have he : extendedPathColors (pathSixCoreColors d) z r
          (pathSixCompress i) =
          extendedPathColors (pathSixCoreColors d) z r
            (pathSixCompress j) := by
        simpa [pathSixChosenColors, hi, hj] using hij
      exact pathSixCompress_injective_away_pendant i j hi hj (hr he)

/-- Among the two pendant choices and four rooted-diamond Hamiltonian paths,
one produces five distinct colors for every outside-to-outside host color. -/
theorem pathSix_color_choice (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) :
    ∃ (s : Bool) (r : Fin 4),
      Function.Injective (pathSixChosenColors d z s r) := by
  have hcore : Function.Injective (pathSixCoreColors d) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 7 => x.val) (hd hij))
  obtain ⟨r, hr⟩ :=
    diamond_color_choice (pathSixCoreColors d) hcore z
  by_cases h : z = d 5
  · refine ⟨false, r, ?_⟩
    have hz : d (pathSixPendantIndex false) ≠ z := by
      rw [h]
      simpa [pathSixPendantIndex] using
        (hd.ne (by decide : (6 : Fin 7) ≠ 5))
    exact pathSixChosenColors_injective d hd z false r hr hz
  · refine ⟨true, r, ?_⟩
    have hz : d (pathSixPendantIndex true) ≠ z := by
      simpa [pathSixPendantIndex] using (Ne.symm h)
    exact pathSixChosenColors_injective d hd z true r hr hz

end ErdosProblems.AntiRamseyPathSixTransfer

namespace ErdosProblems.AntiRamseyPathSixTransfer

open SimpleGraph
open ErdosProblems.AntiRamseyPathFiveUpper

def pathSixSevenColors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 6 → Fin n)
    (hu : Function.Injective u) : Fin 7 → C :=
  fun i =>
    if i = 0 then χ.get (u 2) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 1 then χ.get (u 2) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 2 then χ.get (u 3) (u 4) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 3 then χ.get (u 3) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 4 then χ.get (u 4) (u 5) ((top_adj _ _).mpr (hu.ne (by decide)))
    else if i = 5 then χ.get (u 0) (u 2) ((top_adj _ _).mpr (hu.ne (by decide)))
    else χ.get (u 1) (u 2) ((top_adj _ _).mpr (hu.ne (by decide)))

/-- `true` chooses the first outside vertex as the pendant vertex, and
`false` chooses the second. The other vertex starts the six-vertex path. -/
def pathSixOrderIndex (s : Bool) (r : Fin 4) (i : Fin 6) : Fin 6 :=
  if i = 0 then (if s then 1 else 0)
  else if i = 1 then (if s then 0 else 1)
  else if i = 2 then 2
  else if r = 0 then
    if i = 3 then 4 else if i = 4 then 3 else 5
  else if r = 1 then
    if i = 3 then 5 else if i = 4 then 3 else 4
  else if r = 2 then
    if i = 3 then 4 else if i = 4 then 5 else 3
  else
    if i = 3 then 5 else if i = 4 then 4 else 3

theorem pathSixOrderIndex_injective (s : Bool) (r : Fin 4) :
    Function.Injective (pathSixOrderIndex s r) := by
  cases s <;> fin_cases r <;> decide

theorem pathSix_adj_succ (i : Fin 5) :
    (pathGraph 6).Adj (Fin.castSucc i) (Fin.succ i) := by
  rw [pathGraph_adj]
  left
  simp

def pathSixEdge (i : Fin 5) : (pathGraph 6).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), pathSix_adj_succ i⟩

theorem pathSixEdge_surjective : Function.Surjective pathSixEdge := by
  intro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    change (pathGraph 6).Adj a b at he
    fin_cases a <;> fin_cases b <;>
      first
      | exact ⟨0, Subtype.ext (by rfl)⟩
      | exact ⟨0, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨1, Subtype.ext (by rfl)⟩
      | exact ⟨1, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨2, Subtype.ext (by rfl)⟩
      | exact ⟨2, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨3, Subtype.ext (by rfl)⟩
      | exact ⟨3, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact ⟨4, Subtype.ext (by rfl)⟩
      | exact ⟨4, Subtype.ext (by exact Sym2.eq_swap)⟩
      | exact False.elim (by simp [pathGraph_adj] at he)

/-- The outside-to-outside edge color is unrestricted. -/
theorem rainbow_path_six_of_seven_colors {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (hd : Function.Injective (pathSixSevenColors χ u hu)) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  let z := χ.get (u 0) (u 1) ((top_adj _ _).mpr (hu.ne (by decide)))
  obtain ⟨s, r, hr⟩ := pathSix_color_choice (pathSixSevenColors χ u hu) hd z
  let w : Fin 6 → Fin n := u ∘ pathSixOrderIndex s r
  have hw : Function.Injective w := hu.comp (pathSixOrderIndex_injective s r)
  let φ : (pathGraph 6) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨w, by
      intro i j hij
      exact (top_adj _ _).mpr (hw.ne ((pathGraph 6).ne_of_adj hij))⟩
  let f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hw⟩
  have hcol (i : Fin 5) :
      (EdgeLabeling.pullback χ f.toHom) (pathSixEdge i) =
        pathSixChosenColors (pathSixSevenColors χ u hu) z s r i := by
    cases s <;> fin_cases r <;> fin_cases i <;>
      simp [pathSixEdge, f, φ, w, z, pathSixOrderIndex,
        pathSixChosenColors, pathSixCompress, pathSixCoreColors,
        pathSixPendantIndex, pathSixSevenColors, extendedPathColors,
        diamondPathEdgeIndex, EdgeLabeling.get, Hom.mapEdgeSet,
        Sym2.map_mk, Sym2.eq_swap]
  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  obtain ⟨i, rfl⟩ := pathSixEdge_surjective e₁
  obtain ⟨j, rfl⟩ := pathSixEdge_surjective e₂
  have hij : pathSixChosenColors (pathSixSevenColors χ u hu) z s r i =
      pathSixChosenColors (pathSixSevenColors χ u hu) z s r j := by
    simpa only [hcol] using heq
  exact congrArg pathSixEdge (hr hij)

end ErdosProblems.AntiRamseyPathSixTransfer

namespace ErdosProblems.AntiRamseyPathSixTransfer

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Six named vertices: a four-vertex core at positions `2..5` is complete,
and both outside vertices at positions `0,1` have selected edges to core
vertex `2`. The proof uses five of the six core edges. -/
structure RepresentativeStarCoreOn {V : Type*}
    (G : SimpleGraph V) (u : Fin 6 → V) : Prop where
  a_b : G.Adj (u 2) (u 3)
  a_c : G.Adj (u 2) (u 4)
  a_d : G.Adj (u 2) (u 5)
  b_c : G.Adj (u 3) (u 4)
  b_d : G.Adj (u 3) (u 5)
  c_d : G.Adj (u 4) (u 5)
  x_a : G.Adj (u 0) (u 2)
  y_a : G.Adj (u 1) (u 2)

def pathSixSevenEdgeIndex (i : Fin 7) : Sym2 (Fin 6) :=
  if i = 0 then s(2, 4)
  else if i = 1 then s(2, 5)
  else if i = 2 then s(3, 4)
  else if i = 3 then s(3, 5)
  else if i = 4 then s(4, 5)
  else if i = 5 then s(0, 2)
  else s(1, 2)

theorem pathSixSevenEdgeIndex_injective :
    Function.Injective pathSixSevenEdgeIndex := by
  decide

def representativeSevenEdge {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) : (selectedGraph χ r).edgeSet :=
  if i = 0 then ⟨s(u 2, u 4), h.a_c⟩
  else if i = 1 then ⟨s(u 2, u 5), h.a_d⟩
  else if i = 2 then ⟨s(u 3, u 4), h.b_c⟩
  else if i = 3 then ⟨s(u 3, u 5), h.b_d⟩
  else if i = 4 then ⟨s(u 4, u 5), h.c_d⟩
  else if i = 5 then ⟨s(u 0, u 2), h.x_a⟩
  else ⟨s(u 1, u 2), h.y_a⟩

theorem representativeSevenEdge_val {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) :
    (representativeSevenEdge χ r u h i).val =
      Sym2.map u (pathSixSevenEdgeIndex i) := by
  fin_cases i <;>
    simp [representativeSevenEdge, pathSixSevenEdgeIndex, Sym2.map_mk]

theorem representativeSevenEdge_injective {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u) :
    Function.Injective (representativeSevenEdge χ r u h) := by
  intro i j he
  apply pathSixSevenEdgeIndex_injective
  apply Sym2.map.injective hu
  calc
    Sym2.map u (pathSixSevenEdgeIndex i) =
        (representativeSevenEdge χ r u h i).val :=
      (representativeSevenEdge_val χ r u h i).symm
    _ = (representativeSevenEdge χ r u h j).val := congrArg Subtype.val he
    _ = Sym2.map u (pathSixSevenEdgeIndex j) :=
      representativeSevenEdge_val χ r u h j

theorem pathSixSevenColors_eq_selectedColor {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u)
    (i : Fin 7) :
    pathSixSevenColors χ u hu i =
      selectedColor χ r (representativeSevenEdge χ r u h i) := by
  fin_cases i <;>
    simp [pathSixSevenColors, representativeSevenEdge, selectedColor,
      EdgeLabeling.get]

/-- A representative containing the selected complete four-vertex core and
two edges from distinct outside vertices to a common core vertex forces a
rainbow `pathGraph 6.Copy ⊤` in the original complete-graph coloring. -/
theorem rainbow_path_six_of_representative_starCore {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ) (u : Fin 6 → Fin n)
    (hu : Function.Injective u)
    (h : RepresentativeStarCoreOn (selectedGraph χ r) u) :
    ∃ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hd : Function.Injective (pathSixSevenColors χ u hu) := by
    intro i j he
    apply representativeSevenEdge_injective χ r u hu h
    apply selectedColor_injective χ r
    exact (pathSixSevenColors_eq_selectedColor χ r u hu h i).symm.trans
      (he.trans (pathSixSevenColors_eq_selectedColor χ r u hu h j))
  exact rainbow_path_six_of_seven_colors χ u hu hd

/-- The exact Formal Conjectures no-rainbow-`P₆` premise excludes this
six-vertex structure in *every* one-edge-per-color representative choice. -/
theorem no_representative_starCore_of_no_rainbow_path_six {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (r : RepresentativeChoice χ)
    (hno : ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u : Fin 6 → Fin n) (hu : Function.Injective u) :
    ¬ RepresentativeStarCoreOn (selectedGraph χ r) u := by
  intro h
  obtain ⟨f, hf⟩ := rainbow_path_six_of_representative_starCore χ r u hu h
  exact hno f hf

end ErdosProblems.AntiRamseyPathSixTransfer

namespace ErdosProblems.AntiRamseyPathSixSixConditionalCollapse

open SimpleGraph

def admissible (q : ℕ) : Prop :=
  ∃ χ : TopEdgeLabeling (Fin 6) (Fin q), Function.Surjective χ ∧
    ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
      ¬ IsRainbow f.toHom χ

def collapse {q : ℕ} : Fin q → Fin 8 :=
  fun i => ⟨min i.val 7, by omega⟩

theorem collapse_surjective {q : ℕ} (hq : 8 ≤ q) :
    Function.Surjective (collapse : Fin q → Fin 8) := by
  intro j
  have hj : j.val ≤ 7 := by
    have := j.isLt
    omega
  refine ⟨⟨j.val, by omega⟩, ?_⟩
  apply Fin.ext
  change min j.val 7 = j.val
  exact Nat.min_eq_left hj

/-- A surjective q-color host with no rainbow P6 would collapse to an
eight-color one. Rainbow after collapse implies rainbow before collapse. -/
theorem admissible_collapse {q : ℕ} (hq : 8 ≤ q) :
    admissible q → admissible 8 := by
  rintro ⟨χ, hsurj, hno⟩
  let ψ : TopEdgeLabeling (Fin 6) (Fin 8) := fun e => collapse (χ e)
  refine ⟨ψ, ?_, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := collapse_surjective hq j
    obtain ⟨e, he⟩ := hsurj i
    refine ⟨e, ?_⟩
    simpa [ψ, he] using hi
  · intro f hψ
    apply hno f
    intro e₁ e₂ heq
    apply hψ
    exact congrArg collapse heq

theorem admissible_bddAbove :
    BddAbove {q : ℕ | admissible q} := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin 6)).edgeSet), ?_⟩
  intro q hq
  obtain ⟨χ, hsurj, _⟩ := hq
  simpa using Fintype.card_le_of_surjective χ hsurj

/-- Exact Formal Conjectures anti-Ramsey number upper bound at n=k=6,
conditional on an independently verified eight-color exclusion. -/
theorem antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion
    (h8 : ¬ ∃ χ : TopEdgeLabeling (Fin 6) (Fin 8),
      Function.Surjective χ ∧
      ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
        ¬ IsRainbow f.toHom χ) :
    antiRamseyNum (pathGraph 6) 6 ≤ 7 := by
  have hno : ¬ admissible 8 := h8
  change sSup {q : ℕ | admissible q} ≤ 7
  refine (csSup_le_iff' admissible_bddAbove).2 ?_
  intro q hq
  by_contra hle
  have hq8 : 8 ≤ q := by omega
  exact hno (admissible_collapse hq8 hq)

/-- Conditional first original P6 equality. The checked all-parameter
path lower theorem supplies the reverse direction at (6,6). -/
theorem antiRamseyNum_pathGraph_six_six_eq_seven_of_eight_exclusion
    (h8 : ¬ ∃ χ : TopEdgeLabeling (Fin 6) (Fin 8),
      Function.Surjective χ ∧
      ∀ f : (pathGraph 6).Copy (⊤ : SimpleGraph (Fin 6)),
        ¬ IsRainbow f.toHom χ) :
    antiRamseyNum (pathGraph 6) 6 = 7 := by
  have hupper :=
    antiRamseyNum_pathGraph_six_six_le_seven_of_eight_exclusion h8
  have hlower :=
    ErdosProblems.PathSetLower.pathMaxLower 6 6 (by decide) (by decide)
  norm_num at hlower
  exact Nat.le_antisymm hupper hlower.2

end ErdosProblems.AntiRamseyPathSixSixConditionalCollapse
