module

public import H3ResidualCount1105
public import H3ResidualStar1105
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Original count-to-star seam for h=3. The same arbitrary W and original
K/G occur in every hypothesis and conclusion. Ordinary P4-freedom remains an
explicit hypothesis; the finite seed-first path filling and path-block
argument must derive it before an original whole-cover application. -/

noncomputable section
namespace ErdosProblems.PathUpperReduction.H3CountStar1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CoreElimination
open ErdosProblems.PathUpperReduction.H3ResidualCount1105
open ErdosProblems.PathUpperReduction.H3ResidualStar1105

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exact zero-deficit original seed count and original minimum degrees,
together with ordinary P4 exclusion on the SAME residual, force its actual
center and three independent original leaves. No center, clique or cover is
supplied. -/
theorem original_h3_count_to_residual_star (G : SimpleGraph V) (d : ℕ)
    (K W : Finset V) (hd : 4 ≤ d) (hKcard : K.card = d + 3)
    (hWcard : W.card = d - 1) (hWK : W ⊆ K)
    (hQ : (withinEdges G K).card = d.choose 2 + 3 * d)
    (hseed : ∀ x ∈ K, d ≤ withinDegree G K x)
    (hfree : (pathGraph 4).Free (G.induce ((K \ W : Finset V) : Set V))) :
    ∃ c ∈ K \ W, ((K \ W).erase c).card = 3 ∧
      (∀ x ∈ (K \ W).erase c, G.Adj c x) ∧
      (∀ x ∈ (K \ W).erase c, ∀ y ∈ (K \ W).erase c, ¬ G.Adj x y) := by
  classical
  obtain ⟨hRcard, hRedges⟩ :=
    h3_residual_edges_ge_three_of_exact_seed_count G d K W hd hKcard hWcard hWK hQ
  have hRmin := h3_residual_min_degree_of_original_seed_degree G d K W hd hWcard hseed
  have hmin : ∀ u : ((K \ W : Finset V) : Set V),
      1 ≤ (G.induce ((K \ W : Finset V) : Set V)).degree u := by
    intro u
    have hcount := hRmin u.val u.property
    have hpos : 0 < ((K \ W).filter (fun z => G.Adj u.val z)).card := hcount
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    obtain ⟨hzR, huz⟩ := Finset.mem_filter.mp hz
    have hadj : (G.induce ((K \ W : Finset V) : Set V)).Adj u ⟨z, hzR⟩ := huz
    exact hadj.degree_pos_left
  have hedgeeq : (withinEdges G (K \ W)).card =
      (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card := by
    simpa only [withinEdges] using G.card_filter_edgeFinset_toFinset_subset (K \ W)
  have hedges : 3 ≤ (G.induce ((K \ W : Finset V) : Set V)).edgeFinset.card := by
    rw [← hedgeeq]
    exact hRedges
  exact original_residual_star G K W hRcard hmin hedges hfree

end ErdosProblems.PathUpperReduction.H3CountStar1105

