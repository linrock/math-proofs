module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! No cycle or saturation theorem is imported or used. -/

open SimpleGraph
namespace ErdosProblems.PathUpperReduction.CountCoreBasis

variable {V : Type*} [Fintype V]

noncomputable def GoodCore (G : SimpleGraph V) (d : ℕ) (S : Finset V) : Prop := by
  classical
  exact ∀ x ∈ S, d < (S.filter (fun z => G.Adj x z)).card

noncomputable def degreeCore (G : SimpleGraph V) (d : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ S : Finset V, x ∈ S ∧ GoodCore G d S)

theorem good_subset_core (G : SimpleGraph V) (d : ℕ) (S : Finset V)
    (hS : GoodCore G d S) : S ⊆ degreeCore G d := by
  classical
  intro x hx
  simp only [degreeCore, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨S, hx, hS⟩

theorem degree_core_good (G : SimpleGraph V) (d : ℕ) :
    GoodCore G d (degreeCore G d) := by
  classical
  intro x hx
  obtain ⟨S, hxS, hS⟩ := (Finset.mem_filter.mp hx).2
  have hsub : S.filter (fun z => G.Adj x z) ⊆
      (degreeCore G d).filter (fun z => G.Adj x z) := by
    intro z hz
    obtain ⟨hzS, hxz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨good_subset_core G d S hS hzS, hxz⟩
  exact (hS x hxS).trans_le (Finset.card_le_card hsub)

end ErdosProblems.PathUpperReduction.CountCoreBasis
