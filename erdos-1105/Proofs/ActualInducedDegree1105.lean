module

public import CoreElimination
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
The exact original theorem and whole induced carrier, including isolates,
are preserved.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.ActualInducedDegree1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

noncomputable instance graph_neighborSet_fintype {A : Type*} [Finite A]
    (G : SimpleGraph A) (x : A) : Fintype (G.neighborSet x) := Fintype.ofFinite _

theorem degree_induce_eq_withinDegree (G : SimpleGraph V) (W : Finset V)
    (u : (W : Set V)) :
    (G.induce (W : Set V)).degree u = withinDegree G W u.val := by
  classical
  change ((G.induce (W : Set V)).neighborFinset u).card =
    (W.filter (fun z => G.Adj u.val z)).card
  apply Finset.card_bij (fun v _hv => v.val)
  · intro v hv
    have hadj : (G.induce (W : Set V)).Adj u v :=
      (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mp hv
    refine Finset.mem_filter.mpr ⟨v.property, ?_⟩
    exact hadj
  · intro v₁ _hv₁ v₂ _hv₂ hval
    exact Subtype.ext hval
  · intro z hz
    obtain ⟨hzW, hadj⟩ := Finset.mem_filter.mp hz
    let v : (W : Set V) := ⟨z, hzW⟩
    have hv : v ∈ (G.induce (W : Set V)).neighborFinset u := by
      apply (SimpleGraph.mem_neighborFinset (G.induce (W : Set V)) u v).mpr
      exact hadj
    exact ⟨v, hv, rfl⟩

end ErdosProblems.PathUpperReduction.ActualInducedDegree1105

