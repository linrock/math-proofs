module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PathFiveGraph
public import PathFiveColor

@[expose] public section

/-!
The star coloring gives `n` colors without a rainbow `P₅`, a uniform lower
bound for the `k = 5` slice of Erdős problem 1105, part ii.
-/

namespace ErdosProblems.AntiRamseyPathFive

open SimpleGraph

/-- Every copied five-vertex path has two edges colored zero by the star
construction, so it cannot be rainbow. -/
theorem starColor_noRainbowPathFive {n : ℕ} [NeZero n]
    (f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n))) :
    ¬ IsRainbow f.toHom (starColor n) := by
  intro hrainbow
  obtain ⟨i, j, hij, hai, hbi, haj, hbj⟩ :=
    path_five_copy_two_edges_avoid_vertex f (0 : Fin n)
  have hadj_i : (⊤ : SimpleGraph (Fin n)).Adj
      (f (Fin.castSucc i)) (f (Fin.succ i)) :=
    f.toHom.map_rel (path_five_adj_succ i)
  have hadj_j : (⊤ : SimpleGraph (Fin n)).Adj
      (f (Fin.castSucc j)) (f (Fin.succ j)) :=
    f.toHom.map_rel (path_five_adj_succ j)
  have hcolor_i : (EdgeLabeling.pullback (starColor n) f.toHom) (pathFiveEdge i) = 0 := by
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathFiveEdge] using
      starColor_get_nonincident (f (Fin.castSucc i)) (f (Fin.succ i)) hadj_i hai hbi
  have hcolor_j : (EdgeLabeling.pullback (starColor n) f.toHom) (pathFiveEdge j) = 0 := by
    simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
      EdgeLabeling.get, pathFiveEdge] using
      starColor_get_nonincident (f (Fin.castSucc j)) (f (Fin.succ j)) hadj_j haj hbj
  exact (pathFiveEdge_injective.ne hij)
    (hrainbow (hcolor_i.trans hcolor_j.symm))

theorem antiRamseyNum_pathGraph_five_ge_aux (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    n ≤ antiRamseyNum (pathGraph 5) n := by
  let S : Set ℕ :=
    {k | ∃ χ : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective χ ∧
      ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}
  have hB : BddAbove S := by
    refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
    intro k hk
    obtain ⟨χ, hχ, _⟩ := hk
    simpa using Fintype.card_le_of_surjective χ hχ
  have hmem : n ∈ S := by
    refine ⟨starColor n, starColor_surjective n hn, ?_⟩
    intro f
    exact starColor_noRainbowPathFive f
  change n ≤ sSup S
  exact le_csSup hB hmem

/-- Yuan's star coloring proves the `k = 5` path lower bound for every `n ≥ 5`. -/
theorem antiRamseyNum_pathGraph_five_ge (n : ℕ) (hn : 5 ≤ n) :
    n ≤ antiRamseyNum (pathGraph 5) n := by
  have hne : n ≠ 0 := by omega
  exact @antiRamseyNum_pathGraph_five_ge_aux n ⟨hne⟩ hn

end ErdosProblems.AntiRamseyPathFive
