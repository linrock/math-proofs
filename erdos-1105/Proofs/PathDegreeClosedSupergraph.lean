module

public import PathSpanningNonedgeDeficitV3
public import PathUpperSaturatedFreeSupergraph

@[expose] public section

/-!
The reused saturation and ConeV3 sources have separate strict kernel and
transitive-axiom checks. The carrier has exactly k vertices. No ambient n > k claim is made.
-/

namespace ErdosProblems.PathDegreeClosedSupergraph

open SimpleGraph

/-- A supplied ordinary spanning-path-free graph extends on the same carrier
to a path-free graph whose every missing distinct pair has endpoint degree
sum at most k-2. No connectedness or coloring assumption is imposed. -/
theorem exists_degree_closed_path_free_supergraph {k : ℕ} (hk : 3 ≤ k)
    (G : SimpleGraph (Fin k)) (hfree : (pathGraph k).Free G) :
    ∃ H : SimpleGraph (Fin k), G ≤ H ∧ (pathGraph k).Free H ∧
      ∀ x y : Fin k, x ≠ y → ¬ H.Adj x y →
        H.degree x + H.degree y ≤ k - 2 := by
  classical
  obtain ⟨H, hGH, hHfree, hsat⟩ :=
    ErdosProblems.PathUpperReduction.exists_saturated_free_supergraph
      (pathGraph k) G hfree
  refine ⟨H, hGH, hHfree, ?_⟩
  intro x y hxy hmissing
  exact ErdosProblems.PathSpanningNonedgeDeficit.degree_sum_le_of_spanning_path_augmentation
    hk H hHfree x y hxy hmissing (hsat x y hxy hmissing)

end ErdosProblems.PathDegreeClosedSupergraph
