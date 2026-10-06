module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
Six-vertex classification from the nonuniversal degree cap.
-/

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
