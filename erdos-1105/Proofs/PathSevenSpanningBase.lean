module

public import PathUpperDenseConnectedRepresentativeV2
public import PathDegreeClosedSupergraph
public import PathUpperSpanningDegreeSlots
public import PathMaxLower
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
Exact original-color order-seven spanning base of FC1105(ii). The original surjective coloring and every literal rainbow-copy quantifier are
preserved. Connectedness and closure are derived, not public hypotheses.
-/

namespace ErdosProblems.PathSevenSpanningBase

open SimpleGraph
open ErdosProblems.PathUpperReduction

/-- Every original surjective coloring of K7 avoiding literal rainbow P7
uses at most twelve colors. -/
theorem palette_le_twelve_of_no_rainbow_path_seven {q : ℕ}
    (χ : TopEdgeLabeling (Fin 7) (Fin q)) (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 7).Copy (⊤ : SimpleGraph (Fin 7)),
      ¬ IsRainbow f.toHom χ) : q ≤ 12 := by
  classical
  by_contra hlarge
  have hq : 13 ≤ q := by omega
  have hdense : (7 - 2).choose 2 + 2 ≤ q := by
    have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
    omega
  obtain ⟨r, hconn⟩ := exists_connected_representative_of_dense_palette
    χ hχ (by decide : 0 < 7) hdense
  let G : SimpleGraph (Fin 7) := selectedGraph χ r
  have hGfree : (pathGraph 7).Free G := selectedGraph_free (pathGraph 7) χ r hno
  have hGcount : G.edgeFinset.card = q := selectedGraph_card_edgeFinset χ r
  obtain ⟨H, hGH, hHfree, hclosure⟩ :=
    ErdosProblems.PathDegreeClosedSupergraph.exists_degree_closed_path_free_supergraph
      (by decide : 3 ≤ 7) G hGfree
  have hHconn : H.Connected := SimpleGraph.Connected.mono hGH hconn
  have hHedges : 13 ≤ H.edgeFinset.card := by
    calc
      13 ≤ q := hq
      _ = G.edgeFinset.card := hGcount.symm
      _ ≤ H.edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  have hneTop : H ≠ ⊤ := by
    intro htop
    apply hHfree
    rw [htop]
    exact ⟨Copy.ofLE (pathGraph 7) (⊤ : SimpleGraph (Fin 7)) le_top⟩
  have hclosureLocal : ∀ x y : Fin 7, x ≠ y → ¬ H.Adj x y →
      @SimpleGraph.degree (Fin 7) H x (Subtype.fintype (· ∈ H.neighborSet x)) +
      @SimpleGraph.degree (Fin 7) H y (Subtype.fintype (· ∈ H.neighborSet y)) ≤ 7 - 2 := by
    intro x y hxy hnon
    have h := hclosure x y hxy hnon
    have hx : @SimpleGraph.degree (Fin 7) H x (Subtype.fintype (· ∈ H.neighborSet x)) = H.degree x := by
      congr 1; exact Subsingleton.elim _ _
    have hy : @SimpleGraph.degree (Fin 7) H y (Subtype.fintype (· ∈ H.neighborSet y)) = H.degree y := by
      congr 1; exact Subsingleton.elim _ _
    rw [hx, hy]
    exact h
  obtain ⟨a, _L, ha, htwice, _hLcard, _hLdegree, hCap⟩ :=
    spanning_degree_slots_and_edge_count 7 (by decide) H hHconn hneTop hclosureLocal
  have hc52 : (7 - 1 - 1 : ℕ).choose 2 = 10 := by decide
  have hc42 : (7 - 1 - 2 : ℕ).choose 2 = 6 := by decide
  have hcases : a = 1 ∨ a = 2 := by omega
  rcases hcases with hOne | hTwo
  · subst a
    omega
  · subst a
    omega

/-- Literal order-seven anti-Ramsey upper in the original definition. -/
theorem antiRamseyNum_path_seven_seven_le_twelve :
    antiRamseyNum (pathGraph 7) 7 ≤ 12 := by
  unfold antiRamseyNum
  apply csSup_le'
  rintro q ⟨χ, hχ, hno⟩
  exact palette_le_twelve_of_no_rainbow_path_seven χ hχ hno

/-- Literal order-seven equality, reusing the registered maximum lower bound. -/
theorem antiRamseyNum_path_seven_seven_eq_twelve :
    antiRamseyNum (pathGraph 7) 7 = 12 := by
  apply Nat.le_antisymm antiRamseyNum_path_seven_seven_le_twelve
  have hlower := ErdosProblems.PathSetLower.pathMaxLower 7 7 (by decide) (by decide)
  have hOdd : Odd (7 : ℕ) := by decide
  have hc52 : (7 - 2 : ℕ).choose 2 = 10 := by decide
  have hc22 : (((7 - 1 : ℕ) / 2) - 1).choose 2 = 1 := by decide
  simp only [hOdd, ite_true] at hlower
  omega

end ErdosProblems.PathSevenSpanningBase
