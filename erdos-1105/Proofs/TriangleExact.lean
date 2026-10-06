module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import GallaiColorBound
public import TriangleConstruction
public import TriangleAntiRamsey
public import TriangleCopyReverse

@[expose] public section

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

def admissibleCounts (n : ℕ) : Set ℕ :=
  {k | ∃ χ : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective χ ∧
    ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}

theorem admissibleCounts_bddAbove (n : ℕ) : BddAbove (admissibleCounts n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro k hk
  obtain ⟨χ, hχ, _⟩ := hk
  simpa using Fintype.card_le_of_surjective χ hχ

/-- For `n ≥ 3`, the anti-Ramsey number of the triangle is exactly `n - 1`. -/
theorem antiRamseyNum_cycleGraph_three (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNum (cycleGraph 3) n = n - 1 := by
  change sSup (admissibleCounts n) = n - 1
  apply le_antisymm
  · refine (csSup_le_iff' (admissibleCounts_bddAbove n)).2 ?_
    intro k hk
    obtain ⟨χ, hχ, hno⟩ := hk
    have hrepeat := noRainbowTriangle_of_no_rainbow_cycleGraph_three_copy χ hno
    have hbound := gallai_color_bound χ hrepeat
    have himage : Finset.univ.image χ = Finset.univ :=
      Finset.image_univ_of_surjective hχ
    simpa [himage] using hbound
  · cases n with
    | zero => omega
    | succ m =>
      have hm : m ≠ 0 := by omega
      let : NeZero m := ⟨hm⟩
      have hmem : m ∈ admissibleCounts (m + 1) := by
        refine ⟨predEndpointColor m, predEndpointColor_surjective m, ?_⟩
        exact no_rainbow_cycleGraph_three_copy (predEndpointColor m)
          (fun a b c hab hbc hca => predEndpointColor_noRainbowTriangle a b c hab hbc hca)
      have hle := le_csSup (admissibleCounts_bddAbove (m + 1)) hmem
      simpa using hle

end ErdosProblems.AntiRamseyTriangle
