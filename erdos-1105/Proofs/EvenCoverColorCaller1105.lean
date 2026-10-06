module

public import ActualVertexCoverSellExit1105

@[expose] public section

/-!
Bind the actual SAME-color cover exit to the literal
even maximum, and state its no-rainbow palette consequence. No structural cover existence is proved here.
-/

open SimpleGraph
open ErdosProblems.PathUpperReduction

namespace ErdosProblems.PathUpperReduction.EvenCoverColorCaller1105

theorem rainbow_path_of_actual_vertex_cover_above_even_max {d n q : ℕ}
    (hd : 4 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hq : max ((2 * d).choose 2 + 1)
      ((d - 1).choose 2 + (d - 1) * (n - d + 1) + 2) < q) :
    ∃ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow p.toHom χ := by
  have hd2 : 2 ≤ d := le_trans (by decide : 2 ≤ 4) hd
  have hqB : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  exact ActualVertexCoverSellExit1105.rainbow_path_of_actual_vertex_cover
    hd2 hn χ r X hX hcover hqB

theorem palette_le_linear_of_actual_vertex_cover_and_no_rainbow {d n q : ℕ}
    (hd : 2 ≤ d) (hn : 2 * d + 2 ≤ n)
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (r : RepresentativeChoice χ)
    (X : Finset (Fin n)) (hX : X.card = d)
    (hcover : ∀ u v : Fin n, (selectedGraph χ r).Adj u v → u ∈ X ∨ v ∈ X)
    (hno : ∀ p : (pathGraph (2 * d + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow p.toHom χ) :
    q ≤ (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 := by
  by_contra hq
  have hqB : (d - 1).choose 2 + (d - 1) * (n - d + 1) + 2 < q :=
    lt_of_not_ge hq
  obtain ⟨p, hp⟩ :=
    ActualVertexCoverSellExit1105.rainbow_path_of_actual_vertex_cover
      hd hn χ r X hX hcover hqB
  exact hno p hp

end ErdosProblems.PathUpperReduction.EvenCoverColorCaller1105
