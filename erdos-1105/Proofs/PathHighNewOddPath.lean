module

public import PathHighNewEvenPathV4
public import CycleNewChoiceDegreeV2
public import PathDegreeClosedSupergraph

@[expose] public section

/-! No exact anti-Ramsey equality or full Formal Conjectures path claim is made. -/

namespace ErdosProblems.PathHighNewOdd

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleNewChoiceDegree

variable {C : Type*} [DecidableEq C]

theorem rainbow_odd_path_on_spanning_carrier {ell : ℕ}
    (hell : 2 ≤ ell)
    (χ : TopEdgeLabeling (Fin (2 * ell + 1)) C)
    (hnew : ∀ v : Fin (2 * ell + 1), ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 1)).Copy
        (⊤ : SimpleGraph (Fin (2 * ell + 1))),
      IsRainbow p.toHom χ := by
  classical
  by_contra h
  have hno : ∀ p : (pathGraph (2 * ell + 1)).Copy
      (⊤ : SimpleGraph (Fin (2 * ell + 1))), ¬ IsRainbow p.toHom χ := by
    intro p hp
    exact h ⟨p, hp⟩
  let r : NewChoice χ := canonicalChoice χ
  let G : SimpleGraph (Fin (2 * ell + 1)) := selectedGraph χ r
  have hfree : (pathGraph (2 * ell + 1)).Free G :=
    selectedGraph_free (pathGraph (2 * ell + 1)) χ r hno
  obtain ⟨H, hGH, hHfree, hmissing⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by omega) G hfree
  have hdegree : ∀ v : Fin (2 * ell + 1), ell ≤ H.degree v := by
    intro v
    exact (hnew v).trans
      ((newChoice_degree_ge_newColors χ r v).trans (G.degree_le_of_le hGH))
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    intro x y hxy
    by_contra hnonadj
    have hne : x ≠ y := (top_adj x y).mp hxy
    have hsum := hmissing x y hne hnonadj
    have hx := hdegree x
    have hy := hdegree y
    omega
  have hcopy : Nonempty ((pathGraph (2 * ell + 1)).Copy H) := by
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph (2 * ell + 1))
      (⊤ : SimpleGraph (Fin (2 * ell + 1))) le_top⟩
  exact hHfree hcopy

/-- Every original NEW-color set has at least ell colors, so the original
complete-host coloring has a rainbow path on 2 * ell + 1 vertices. -/
theorem exists_rainbow_odd_path_of_high_new {ell n : ℕ}
    (hell : 2 ≤ ell) (hn : 2 * ell + 1 ≤ n)
    (χ : TopEdgeLabeling (Fin n) C)
    (hnew : ∀ v : Fin n, ell ≤ (newColors χ v).card) :
    ∃ p : (pathGraph (2 * ell + 1)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  classical
  by_cases hspan : n = 2 * ell + 1
  · subst n
    exact rainbow_odd_path_on_spanning_carrier hell χ hnew
  · obtain ⟨p, hp⟩ :=
      ErdosProblems.PathHighNew.exists_rainbow_even_path_of_high_new
        hell (by omega) χ hnew
    have hab : 2 * ell + 1 ≤ 2 * ell + 2 := by omega
    -- The checked Stage2V6 prefix/composition helpers are private.
    -- This literal adapter uses the same Fin.castLE and mapEdgeSet APIs.
    let q : (pathGraph (2 * ell + 1)).Copy (pathGraph (2 * ell + 2)) :=
      { toHom :=
          { toFun := Fin.castLE hab
            map_rel' := by
              intro i j hij
              apply pathGraph_adj.mpr
              simpa only [Fin.val_castLE] using pathGraph_adj.mp hij }
        injective' := Fin.castLE_injective hab }
    have hmap (e : (pathGraph (2 * ell + 1)).edgeSet) :
        (p.comp q).toHom.mapEdgeSet e =
          p.toHom.mapEdgeSet (q.toHom.mapEdgeSet e) := by
      apply Subtype.ext
      simpa only [Copy.comp, Hom.mapEdgeSet, Hom.coe_comp] using
        (Sym2.map_map (f := q.toHom) (g := p.toHom) e.val).symm
    refine ⟨p.comp q, ?_⟩
    intro e d heq
    apply Hom.mapEdgeSet.injective q.toHom q.injective
    apply hp
    simpa only [EdgeLabeling.pullback_apply, hmap] using heq

end ErdosProblems.PathHighNewOdd
