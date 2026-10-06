module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import PathSetBridge
public import PathSetParameters
public import PathSetColor

@[expose] public section

/-!
Yuan's fixed-set construction proves the second lower-bound term of the
proposed exact anti-Ramsey formula for paths, in the original quantified
range `n ≥ k ≥ 5`.
-/

namespace ErdosProblems.PathSetLower

open SimpleGraph

def admissiblePathCounts (k n : ℕ) : Set ℕ :=
  {q | ∃ χ : TopEdgeLabeling (Fin n) (Fin q), Function.Surjective χ ∧
    ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ}

theorem admissiblePathCounts_bddAbove (k n : ℕ) :
    BddAbove (admissiblePathCounts k n) := by
  refine ⟨Fintype.card ((⊤ : SimpleGraph (Fin n)).edgeSet), ?_⟩
  intro q hq
  obtain ⟨χ, hsurj, _⟩ := hq
  simpa using Fintype.card_le_of_surjective χ hsurj

/-- Yuan's `(ℓ - 1)`-hub construction gives its exact color count as a lower
bound on `antiRamseyNum (pathGraph k) n` for every `n ≥ k ≥ 5`. -/
theorem pathSetLower (k n : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    (fixedSetSize k).choose 2 +
      fixedSetSize k * (n - fixedSetSize k) + outsidePaletteSize k
        ≤ antiRamseyNum (pathGraph k) n := by
  let t := fixedSetSize k
  let ε := outsidePaletteSize k
  change t.choose 2 + t * (n - t) + ε ≤ antiRamseyNum (pathGraph k) n
  have hε : 0 < ε := outsidePaletteSize_pos k
  have hε₂ : ε ≤ 2 := outsidePaletteSize_le_two k
  have hgap : 2 * t + ε < k - 1 := fixedSetSize_gap k hk
  have hthree : t + 3 ≤ n := fixedSetSize_three_outside hk hkn
  have ht : t ≤ n := by omega
  let e₀ := outsideZeroEdge hthree
  let e₁ := outsideOneEdge hthree
  have h₀ : e₀ ∉ incidentEdgeFinset t n := outsideZeroEdge_not_incident hthree
  have h₁ : e₁ ∉ incidentEdgeFinset t n := outsideOneEdge_not_incident hthree
  have hne : e₀ ≠ e₁ := outsideEdges_ne hthree
  let χ := setColor ht hε e₁
  have hsurj : Function.Surjective χ :=
    setColor_surjective ht hε hε₂ e₀ e₁ h₀ h₁ hne
  have hno : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ := by
    have hpalette :
        ∀ a b : Fin n, (hab : a ≠ b) →
          t ≤ a.val → t ≤ b.val →
          ∃ z : Fin ε,
            χ.get a b ((top_adj a b).2 hab) = freshSetColor ht z := by
      intro a b hab ha hb
      refine ⟨twoPaletteColor hε e₁ (completeEdge a b hab), ?_⟩
      simpa [χ] using setColor_get_outside ht hε e₁ a b hab ha hb
    have hcopy :=
      noRainbowPath_of_smallOutsidePalette
        (m := k - 1) (n := n) (t := t) (ε := ε)
        hε hgap χ (freshSetColor ht) hpalette
    have hkEq : k - 1 + 1 = k := by omega
    rw [hkEq] at hcopy
    exact hcopy
  change t.choose 2 + t * (n - t) + ε ≤ sSup (admissiblePathCounts k n)
  apply le_csSup (admissiblePathCounts_bddAbove k n)
  exact ⟨χ, hsurj, hno⟩

/-- The same lower bound in the literal second-term notation of Formal
Conjectures #1105, part ii. -/
theorem secondTerm_lower (k n : ℕ) (hk : 5 ≤ k) (hkn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    (ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε
      ≤ antiRamseyNum (pathGraph k) n := by
  dsimp
  have hℓ : 1 ≤ (k - 1) / 2 := by omega
  have hℓn : (k - 1) / 2 ≤ n := by omega
  have hsub : n - ((k - 1) / 2 - 1) = n - (k - 1) / 2 + 1 := by omega
  have hres := pathSetLower k n hk hkn
  change ((k - 1) / 2 - 1).choose 2 +
    ((k - 1) / 2 - 1) * (n - ((k - 1) / 2 - 1)) +
    (if Odd k then 1 else 2) ≤ antiRamseyNum (pathGraph k) n at hres
  rw [hsub] at hres
  exact hres

end ErdosProblems.PathSetLower
