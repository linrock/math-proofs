module

public import PathGeneralFiniteWindowReduction
public import PathMaxLower

@[expose] public section

/-!
Equivalence reducing the universal path anti-Ramsey formula (`erdos_1105.parts.ii`)
to upper bounds on the finite host windows `2ℓ + 1 ≤ n ≤ 2ℓ + 1 + ⌊(ℓ - 3) / 2⌋`
(odd paths) and `2ℓ + 2 ≤ n ≤ 2ℓ + 2 + ⌊(ℓ - 1) / 2⌋` (even paths), by combining
high-NEW vertex-deletion propagation (`PathGeneralFiniteWindowReduction`) with
the universal path lower bound (`PathMaxLower`).
-/

namespace ErdosProblems.LiteralPathEqualityFiniteWindows1105

open SimpleGraph

/-- The full literal FC1105(ii) equality is equivalent to all original odd
and even finite-window upper bounds; no coloring or graph premise is supplied. -/
theorem original_path_equality_iff_finite_windows :
    (∀ k n : ℕ, 5 ≤ k → k ≤ n →
      let ell := (k - 1) / 2
      let eps := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + eps)) ↔
    ((∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 1 ≤ n → n ≤ 2 * ell + 1 + (ell - 3) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 1)) n ≤
          max ((2 * ell - 1).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 1)) ∧
      (∀ ell : ℕ, 2 ≤ ell → ∀ n : ℕ,
        2 * ell + 2 ≤ n → n ≤ 2 * ell + 2 + (ell - 1) / 2 →
        antiRamseyNum (pathGraph (2 * ell + 2)) n ≤
          max ((2 * ell).choose 2 + 1)
            ((ell - 1).choose 2 + (ell - 1) * (n - ell + 1) + 2))) := by
  constructor
  · intro hall
    apply ErdosProblems.PathGeneralFiniteWindowReduction.original_path_upper_iff_finite_windows.mp
    intro k n hk hn
    exact le_of_eq (hall k n hk hn)
  · intro hwindows
    have hupper :=
      ErdosProblems.PathGeneralFiniteWindowReduction.original_path_upper_iff_finite_windows.mpr hwindows
    intro k n hk hn
    exact Nat.le_antisymm (hupper k n hk hn)
      (ErdosProblems.PathSetLower.pathMaxLower k n hk hn)

end ErdosProblems.LiteralPathEqualityFiniteWindows1105
