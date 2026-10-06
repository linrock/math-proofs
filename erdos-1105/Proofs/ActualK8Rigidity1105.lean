module

public import ActualCutDegreeLedger1105
public import G8DegreeDichotomy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic

@[expose] public section

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
