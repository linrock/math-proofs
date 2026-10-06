module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import CycleBlockBridgeCore

@[expose] public section

/-!
An exact `IsRainbow` facade for the raw ordered-block coloring. This proves
non-rainbowness of every injective `cycleGraph k` copy under a small-fiber block
map. The raw palette is not yet counted or relabeled to `Fin M`.
-/

namespace ErdosProblems.AntiRamseyCycle

open SimpleGraph

/-- The raw ordered-block color of a complete-graph edge. -/
def rawOrderedBlockLabeling {n t : ℕ} (π : Fin n → Fin t) :
    TopEdgeLabeling (Fin n) (Sum (Sym2 (Fin n)) (Fin t)) :=
  fun e => orderedBlockColor π e.val

/-- Every copied cycle visits two blocks and repeats a raw color when each
block has fewer vertices than the cycle. -/
theorem rawOrderedBlockLabeling_noRainbow_copy
    {k n t : ℕ} (hk : 3 ≤ k) (hn : k ≤ n)
    (π : Fin n → Fin t)
    (hsmall : ∀ b : Fin t,
      (Finset.univ.filter (fun x : Fin n => π x = b)).card < k) :
    ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom (rawOrderedBlockLabeling π) := by
  intro f hf
  apply not_injective_raw_orderedBlockColor_pullback hk hn π hsmall f
  exact hf

end ErdosProblems.AntiRamseyCycle
