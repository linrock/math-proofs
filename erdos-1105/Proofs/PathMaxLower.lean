module

public import PathSetLower
public import PathCliqueColor

@[expose] public section

/-!
Combines the `(k - 2)`-clique lower bound (`PathCliqueColor`) and the
`(ℓ - 1)`-hub lower bound (`PathSetLower`) to establish the universal lower-bound
direction of Part (ii) of Erdős Problem 1105 for all `n ≥ k ≥ 5`.
-/

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
