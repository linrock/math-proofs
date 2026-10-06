module

public import PathFiveDenseComponent
public import DenseFourDiamondFinite
public import RepresentativeDiamondTransfer
public import PathFiveLower

@[expose] public section

/-!
The exact `k = 5` slice of the Formal Conjectures path statement. The upper
bound combines the selected one-edge-per-color graph with the connected
`P₅`-free extremal theorem, a dense four-vertex diamond, and the already
verified diamond-to-rainbow path transfer. This does not settle `k > 5`.
-/

namespace ErdosProblems.AntiRamseyPathFiveExact

open SimpleGraph
set_option linter.style.haveILetI false

/-- Every admissible `P₅` coloring on at least five vertices uses at most
`n` colors. -/
theorem admissible_path_five_color_count_le (n q : ℕ) (hn : 5 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ) : q ≤ n := by
  classical
  let G : SimpleGraph (Fin n) :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph χ hχ
  have hfree : (pathGraph 5).Free G :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph_free
      (pathGraph 5) χ hχ hno
  have hcard : G.edgeFinset.card = q :=
    ErdosProblems.AntiRamseyRepresentative.representativeGraph_card_edgeFinset χ hχ
  have hnat : Nat.card G.edgeSet = q := by
    rw [Nat.card_eq_fintype_card]
    rw [G.card_edgeSet]
    exact hcard
  by_contra hnot
  have hmore :
      n < (@SimpleGraph.edgeFinset (Fin n) G (SimpleGraph.fintypeEdgeSet G)).card := by
    have hc :
        (@SimpleGraph.edgeFinset (Fin n) G (SimpleGraph.fintypeEdgeSet G)).card =
          Nat.card G.edgeSet := by
      letI : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
      rw [Nat.card_eq_fintype_card]
      exact (G.card_edgeSet).symm
    omega
  obtain ⟨C, hfour, hfive⟩ :=
    ErdosProblems.AntiRamseyPathFiveComponents.exists_dense_four_component
      hn G hfree hmore
  obtain ⟨u, hu, h02, h03, h12, h13, h23⟩ :=
    ErdosProblems.AntiRamseyPathFiveDiamond.dense_component_has_diamond
      G C hfour hfive
  have hdiamond : ErdosProblems.AntiRamseyPathFiveTransfer.DiamondOn G
      (u 0) (u 1) (u 2) (u 3) := ⟨h02, h03, h12, h13, h23⟩
  exact (ErdosProblems.AntiRamseyPathFiveTransfer.no_representative_diamond_of_no_rainbow_path_five
    hn χ hχ hno u hu) hdiamond

/-- The `P₅` anti-Ramsey number is at most `n` for every `n ≥ 5`. -/
theorem antiRamseyNum_pathGraph_five_le (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n ≤ n := by
  classical
  let S : Set ℕ :=
    {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
      ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
        ¬IsRainbow f.toHom χ}
  have hB : BddAbove S := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro q hq
    obtain ⟨χ, hχ, _⟩ := hq
    simpa using Fintype.card_le_of_surjective χ hχ
  change sSup S ≤ n
  refine (csSup_le_iff' hB).2 ?_
  intro q hq
  obtain ⟨χ, hχ, hno⟩ := hq
  exact admissible_path_five_color_count_le n q hn χ hχ hno

/-- The exact five-vertex path answer at every original-domain `n`. -/
theorem antiRamseyNum_pathGraph_five_eq (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n = n := by
  exact Nat.le_antisymm (antiRamseyNum_pathGraph_five_le n hn)
    (ErdosProblems.AntiRamseyPathFive.antiRamseyNum_pathGraph_five_ge n hn)

/-- The literal right-hand side of `erdos_1105.parts.ii` simplifies to `n`
when `k = 5` and `n ≥ 5`. -/
theorem path_five_formal_rhs_eq (n : ℕ) (hn : 5 ≤ n) :
    max ((5 - 2 : ℕ).choose 2 + 1)
      (((((5 - 1 : ℕ) / 2) - 1).choose 2) +
        (((5 - 1 : ℕ) / 2) - 1) * (n - ((5 - 1 : ℕ) / 2) + 1) +
          (if Odd (5 : ℕ) then 1 else 2)) = n := by
  norm_num
  omega

/-- The `k = 5` instance of the pinned Formal Conjectures path formula. -/
theorem path_five_formal_slice (n : ℕ) (hn : 5 ≤ n) :
    antiRamseyNum (pathGraph 5) n =
      max ((5 - 2 : ℕ).choose 2 + 1)
        (((((5 - 1 : ℕ) / 2) - 1).choose 2) +
          (((5 - 1 : ℕ) / 2) - 1) * (n - ((5 - 1 : ℕ) / 2) + 1) +
            (if Odd (5 : ℕ) then 1 else 2)) := by
  rw [antiRamseyNum_pathGraph_five_eq n hn, path_five_formal_rhs_eq n hn]

end ErdosProblems.AntiRamseyPathFiveExact
