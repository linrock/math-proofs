module

public import FractionRectangle2
public import MomentBound2


@[expose] public section

/-!
# Second-moment bound for bad fibers of rectangle families

Specializes the weighted indicator square expansion (`second_moment_le_pair_intersections`)
to the bad fiber fractions `fraction (badFiber S T x)` of a product rectangle
family.
-/

namespace Erdos2.Rectangles

open Finset

theorem rectangle_second_moment_le {Ω β I : Type*}
    [Fintype Ω] [Fintype β] [Fintype I] [DecidableEq Ω] [DecidableEq β]
    [Nonempty β] (w : Ω → ℝ) (S : I → Finset Ω) (T : I → Finset β)
    (H : I → I → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hH : ∀ i j, (∑ x ∈ S i ∩ S j, w x) ≤ H i j) :
    (∑ x, w x * (fraction (badFiber S T x)) ^ 2) ≤
      ∑ i, ∑ j, fraction (T i) * fraction (T j) * H i j := by
  exact Erdos2.Moments.second_moment_le_pair_intersections w
    (fun i => fraction (T i)) S (fun x => fraction (badFiber S T x)) H hw
    (fun i => fraction_nonneg (T i))
    (fun x => fraction_nonneg (badFiber S T x))
    (fun x => badFiber_fraction_le S T x) hH

end Erdos2.Rectangles
