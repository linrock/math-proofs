module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import GallaiColorBound

@[expose] public section

namespace ErdosProblems.AntiRamseyTriangle

open SimpleGraph

/-- A complete edge labeling with no rainbow triangle has no rainbow copy of `C₃`. -/
theorem no_rainbow_cycleGraph_three_copy {n : ℕ} {C : Type*}
    (χ : TopEdgeLabeling (Fin n) C) (hχ : NoRainbowTriangle χ) :
    ∀ f : (cycleGraph 3).Copy (⊤ : SimpleGraph (Fin n)), ¬ IsRainbow f.toHom χ := by
  intro f hf
  let a : Fin n := f 0
  let b : Fin n := f 1
  let c : Fin n := f 2
  have hab : a ≠ b := f.injective.ne (by decide)
  have hbc : b ≠ c := f.injective.ne (by decide)
  have hca : c ≠ a := f.injective.ne (by decide)
  rcases hχ a b c hab hbc hca with h₁ | h₂ | h₃
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₁
    have he : (⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₂
    have he : (⟨s((1 : Fin 3), 2), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)
  · have : (EdgeLabeling.pullback χ f.toHom) ⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ =
        (EdgeLabeling.pullback χ f.toHom) ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ := by
      simpa [EdgeLabeling.pullback_apply, Hom.mapEdgeSet, Sym2.map_mk,
        EdgeLabeling.get, a, b, c] using h₃
    have he : (⟨s((2 : Fin 3), 0), by simp [cycleGraph_three_eq_top]⟩ :
        (cycleGraph 3).edgeSet) ≠
        ⟨s((0 : Fin 3), 1), by simp [cycleGraph_three_eq_top]⟩ := by decide
    exact he (hf this)

end ErdosProblems.AntiRamseyTriangle
