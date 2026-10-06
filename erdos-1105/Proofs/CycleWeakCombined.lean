module

public import CycleWeakCount
public import CycleWeakArithmetic

@[expose] public section

namespace ErdosProblems.AntiRamseyWeakCount

open Finset SimpleGraph
open ErdosProblems.AntiRamseyTriangle

/-- A conditional cycle-coefficient bound for the number of colors realized by an
edge coloring. The block map and quotient coloring are supplied explicitly.
Every block is nonempty and has fewer than `k` vertices. This theorem does not
construct the blocks from avoidance of a rainbow `k`-cycle. -/
theorem realized_colors_le_cycle_linear_of_weak_blocks {V C : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (k t n : ℕ) (hk : 3 ≤ k) (ht : 1 ≤ t)
    (χ : TopEdgeLabeling V C) (b : V → Fin t)
    (ψ : TopEdgeLabeling (Fin t) C)
    (hcross : ∀ (a d : V) (had : a ≠ d) (hbd : b a ≠ b d),
      χ.get a d had = ψ.get (b a) (b d) hbd)
    (htriple : NoRainbowTriangle ψ)
    (hspos : ∀ i, 1 ≤ (blockFiber b i).card)
    (hsupper : ∀ i, (blockFiber b i).card ≤ k - 1)
    (hsum : ∑ i : Fin t, (blockFiber b i).card = n) :
    ((Finset.univ.image χ).card : ℝ) ≤
      (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ) - 1 := by
  have hcount := realized_colors_le_block_edges_add χ b ψ hcross htriple
  have hcount_real : ((Finset.univ.image χ).card : ℝ) ≤
      (((∑ i : Fin t, (blockFiber b i).card.choose 2 : ℕ) : ℕ) : ℝ) +
        ((t - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  exact hcount_real.trans
    (block_arithmetic_linear_bound k t n hk ht
      (fun i => (blockFiber b i).card) hspos hsupper hsum)

end ErdosProblems.AntiRamseyWeakCount
