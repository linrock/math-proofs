module

public import PathSpanningNonedgeDeficitV3

@[expose] public section

/-!
Generic missing-pair spanning-path closure on `Fin N` via the `Option` cone
contrapositive.
-/

namespace ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105

open SimpleGraph
open ErdosProblems.PathSpanningNonedgeDeficit

/-- Adding one original distinct missing pair preserves ordinary spanning
path freedom on the SAME `Fin N` carrier when the ORIGINAL whole-carrier
endpoint degrees sum to at least `N - 1`. No path endpoint is prescribed. -/
theorem pathGraph_free_after_adding_missing_pair
    {N : ℕ} (hN : 3 ≤ N)
    (G : SimpleGraph (Fin N)) (hfree : (pathGraph N).Free G)
    (u v : Fin N) (huv : u ≠ v) (hmissing : ¬ G.Adj u v)
    (hsum : N - 1 ≤ G.degree u + G.degree v) :
    (pathGraph N).Free (augment G u v) := by
  classical
  intro hcopy
  have hbound : G.degree u + G.degree v ≤ N - 2 :=
    ErdosProblems.PathSpanningNonedgeDeficit.degree_sum_le_of_spanning_path_augmentation
      hN G hfree u v huv hmissing hcopy
  omega

end ErdosProblems.PathUpperReduction.GenericPathMissingPairClosure1105
