module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

/-!
An ordinary eight-vertex graph degree consequence of a nonedge degree-sum bound.
This file uses no color, path, connectivity, or edge-count hypothesis.
-/

namespace Erdos1105.PathUpperDegree

theorem eight_degree_dichotomy
    (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (hmin : ∀ v : Fin 8, 2 ≤ G.degree v)
    (hclosure : ∀ x y : Fin 8, x ≠ y → ¬G.Adj x y →
      G.degree x + G.degree y ≤ 6)
    (hlow : (Finset.univ.filter (fun v : Fin 8 => G.degree v = 2)).card ≤ 2) :
    ∀ v : Fin 8, G.degree v = 2 ∨ G.degree v = 3 ∨ G.degree v = 7 := by
  classical
  intro v
  by_cases hlarge : 5 ≤ G.degree v
  · have huniv : G.IsUniversal v := by
      intro w hne
      by_contra hnon
      have hsum := hclosure v w hne hnon
      have hminw := hmin w
      omega
    have hseven : G.degree v = 7 := by
      have h := (G.degree_eq_card_sub_one v).mpr huniv
      simpa using h
    exact Or.inr (Or.inr hseven)
  · have hnotfour : G.degree v ≠ 4 := by
      intro hfour
      have hcomp : Gᶜ.degree v = 3 := by
        rw [G.degree_compl]
        norm_num [hfour]
      have hcompCard : (Gᶜ.neighborFinset v).card = 3 := by
        calc
          (Gᶜ.neighborFinset v).card = Gᶜ.degree v :=
            Gᶜ.card_neighborFinset_eq_degree v
          _ = 3 := hcomp
      have hsubset : Gᶜ.neighborFinset v ⊆
          Finset.univ.filter (fun y : Fin 8 => G.degree y = 2) := by
        intro y hy
        have hyAdj : Gᶜ.Adj v y := (Gᶜ.mem_neighborFinset v y).mp hy
        obtain ⟨hne, hnon⟩ := (G.compl_adj v y).mp hyAdj
        have hsum := hclosure v y hne hnon
        have hminy := hmin y
        have htwo : G.degree y = 2 := by omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
      have hthree : 3 ≤
          (Finset.univ.filter (fun y : Fin 8 => G.degree y = 2)).card := by
        have h := Finset.card_le_card hsubset
        simpa only [hcompCard] using h
      omega
    have hminv := hmin v
    omega

end Erdos1105.PathUpperDegree
