module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import GallaiColorBound

@[expose] public section

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

/-- The absence of a rainbow injective copy of `C₃` forces every triangle to repeat a color. -/
theorem noRainbowTriangle_of_no_rainbow_cycleGraph_three_copy {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ) : NoRainbowTriangle χ := by
  intro a b c hab hbc hca
  by_contra hrepeat
  have h₁ : χ.get a b hab ≠ χ.get b c hbc := by
    intro heq
    exact hrepeat (Or.inl heq)
  have h₂ : χ.get b c hbc ≠ χ.get c a hca := by
    intro heq
    exact hrepeat (Or.inr (Or.inl heq))
  have h₃ : χ.get c a hca ≠ χ.get a b hab := by
    intro heq
    exact hrepeat (Or.inr (Or.inr heq))
  let v : Fin 3 → Fin n := fun i => if i = 0 then a else if i = 1 then b else c
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [v, hab, hab.symm, hbc, hbc.symm, hca, hca.symm] at hij ⊢
  let φ : (cycleGraph 3) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨v, by
      intro i j hij
      exact (top_adj _ _).mpr (hv.ne ((cycleGraph 3).ne_of_adj hij))⟩
  let f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hv⟩
  let e₁ : (cycleGraph 3).edgeSet :=
    ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩
  let e₂ : (cycleGraph 3).edgeSet :=
    ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩
  let e₃ : (cycleGraph 3).edgeSet :=
    ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩
  have hedges : ∀ e : (cycleGraph 3).edgeSet,
      e = e₁ ∨ e = e₂ ∨ e = e₃ := by
    decide
  have hcol₁ : (EdgeLabeling.pullback χ f.toHom) e₁ = χ.get a b hab := by
    simp [e₁, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  have hcol₂ : (EdgeLabeling.pullback χ f.toHom) e₂ = χ.get b c hbc := by
    simp [e₂, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  have hcol₃ : (EdgeLabeling.pullback χ f.toHom) e₃ = χ.get c a hca := by
    simp [e₃, f, φ, v, EdgeLabeling.get, Hom.mapEdgeSet, Sym2.map_mk]
  apply hno f
  intro x y hxy
  rcases hedges x with hx | hx | hx <;>
    rcases hedges y with hy | hy | hy <;>
    subst x <;> subst y
  · rfl
  · exact (h₁ (by simpa only [hcol₁, hcol₂] using hxy)).elim
  · exact (h₃ (by simpa only [hcol₃, hcol₁] using hxy.symm)).elim
  · exact (h₁ (by simpa only [hcol₁, hcol₂] using hxy.symm)).elim
  · rfl
  · exact (h₂ (by simpa only [hcol₂, hcol₃] using hxy)).elim
  · exact (h₃ (by simpa only [hcol₃, hcol₁] using hxy)).elim
  · exact (h₂ (by simpa only [hcol₂, hcol₃] using hxy.symm)).elim
  · rfl

end ErdosProblems.AntiRamseyTriangle
