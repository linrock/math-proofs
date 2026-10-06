module

public import CycleFullBlockPalette
public import CycleBlockArithmetic

@[expose] public section

/-!
Numerical lower bound `⌊n / (k - 1)⌋ * (choose(k - 1, 2) + 1) - 1 ≤ antiRamseyNum (cycleGraph k) n`
from the injection of full `(k - 1)`-block raw palette tags.
-/

namespace ErdosProblems.AntiRamseyCycleCounted

open SimpleGraph
open ErdosProblems.AntiRamseyCycle
open ErdosProblems.AntiRamseyCycleBlockCount

/-- The checked full-block tag injection supplies a numerical lower bound
for the realized raw palette. -/
theorem fullBlock_rawPalette_card_lower (m n : ℕ)
    (hm : 0 < m) (hq : 0 < n / m) :
    n / m * (m.choose 2 + 1) - 1 ≤
      (rawPalette (consecutiveBlockMap m n)).card := by
  classical
  have hedge :
      Fintype.card ((⊤ : SimpleGraph (Fin m)).edgeSet) = m.choose 2 := by
    rw [SimpleGraph.card_edgeSet,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  have hdomain :
      Fintype.card
          (Sum (Fin (n / m) × (⊤ : SimpleGraph (Fin m)).edgeSet)
            (Fin (n / m - 1))) =
        n / m * m.choose 2 + (n / m - 1) := by
    simp only [Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, hedge]
  have hle := Fintype.card_le_of_injective
    (fullBlockRawWitness m n hm hq)
    (fullBlockRawWitness_injective m n hm hq)
  have hraw : n / m * m.choose 2 + (n / m - 1) ≤
      (rawPalette (consecutiveBlockMap m n)).card := by
    simpa only [hdomain, Fintype.card_coe] using hle
  have hformula :
      n / m * m.choose 2 + (n / m - 1) =
        n / m * (m.choose 2 + 1) - 1 := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [← hformula]
  exact hraw

/-- For every original `n ≥ k ≥ 3`, full `(k−1)` blocks alone provide
the indicated number of nonrainbow colors on `K_n`. -/
theorem cycle_fullBlock_antiRamseyNum_lower (k n : ℕ)
    (hk : 3 ≤ k) (hn : k ≤ n) :
    n / (k - 1) * ((k - 1).choose 2 + 1) - 1 ≤
      antiRamseyNum (cycleGraph k) n := by
  have hm : 0 < k - 1 := by omega
  have hq : 0 < n / (k - 1) :=
    Nat.div_pos (by omega : k - 1 ≤ n) hm
  have hpalette := fullBlock_rawPalette_card_lower (k - 1) n hm hq
  have himage := rawPalette_card_le_antiRamseyNum hk hn
    (consecutiveBlockMap (k - 1) n)
    (cycleBlockMap_small_fibers k n hk)
  exact hpalette.trans himage

/-- Two full three-vertex blocks on six vertices give seven realized
colors without a rainbow four-cycle. -/
theorem cycle_four_six_antiRamseyNum_ge_seven :
    7 ≤ antiRamseyNum (cycleGraph 4) 6 := by
  simpa using cycle_fullBlock_antiRamseyNum_lower 4 6
    (by decide : 3 ≤ 4) (by decide : 4 ≤ 6)

end ErdosProblems.AntiRamseyCycleCounted
