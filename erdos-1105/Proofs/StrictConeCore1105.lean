module

public import CountCoreBasis
public import UniformCone1105
public import Mathlib.Data.Finset.Option
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Transport the strict empty-core condition back to the SAME graph.
No saturation, coloring, connectivity or chosen-kernel premise is needed. -/

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.StrictConeCore1105
open CountCoreBasis UniformCone1105

theorem degreeCore_eq_empty_of_cone_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : SimpleGraph (Option V)) (d : ℕ)
    (hcone : cone G ≤ H) (hH : degreeCore H (d + 1) = ∅) :
    degreeCore G d = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let C := degreeCore G d
  have hxC : x ∈ C := hx
  have hC : GoodCore G d C := degree_core_good G d
  have hsmall : (C.filter (fun z => G.Adj x z)).card < C.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hxx := (Finset.mem_filter.mp (heq.symm ▸ hxC)).2
    exact G.loopless.irrefl x hxx
  have hsize : d + 2 ≤ C.card := by
    have := hC x hxC
    omega
  let T := C.insertNone
  have hT : GoodCore H (d + 1) T := by
    intro a ha
    cases a with
    | none =>
      have hsub : C.image some ⊆ T.filter (fun z => H.Adj none z) := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨Finset.some_mem_insertNone.mpr hy, ?_⟩
        exact hcone (by trivial : (cone G).Adj none (some y))
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective C (Option.some_injective V)] at hc
      omega
    | some y =>
      have hy : y ∈ C := Finset.some_mem_insertNone.mp ha
      have hsub : (C.filter (fun z => G.Adj y z)).insertNone ⊆
          T.filter (fun z => H.Adj (some y) z) := by
        intro z hz
        cases z with
        | none =>
          exact Finset.mem_filter.mpr
            ⟨Finset.none_mem_insertNone,
              hcone (by trivial : (cone G).Adj (some y) none)⟩
        | some z =>
          obtain ⟨hzC, hyz⟩ := Finset.mem_filter.mp
            (Finset.some_mem_insertNone.mp hz)
          exact Finset.mem_filter.mpr
            ⟨Finset.some_mem_insertNone.mpr hzC, hcone hyz⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insertNone] at hc
      have := hC y hy
      omega
  have hnone : none ∈ degreeCore H (d + 1) :=
    good_subset_core H (d + 1) T hT Finset.none_mem_insertNone
  simp [hH] at hnone

end ErdosProblems.PathUpperReduction.StrictConeCore1105

example {V : Type*} [Fintype V] (G : SimpleGraph V)
    (H : SimpleGraph (Option V)) (d : ℕ)
    (hcone : ErdosProblems.PathUpperReduction.UniformCone1105.cone G ≤ H)
    (hH : ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore H (d + 1) = ∅) :
    ErdosProblems.PathUpperReduction.CountCoreBasis.degreeCore G d = ∅ :=
  ErdosProblems.PathUpperReduction.StrictConeCore1105.degreeCore_eq_empty_of_cone_le G H d hcone hH
