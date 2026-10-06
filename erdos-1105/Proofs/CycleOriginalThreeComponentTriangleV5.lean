module

public import CycleOriginalCrossComponentConstancyV7
public import CycleQuotientTriangleSpliceV3

@[expose] public section

/-!
Three-component triangle reduction for Claim 4 on the original host coloring.
-/

namespace ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleComponentCyclicIndex
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion
open ErdosProblems.AntiRamseyCycleOriginalCrossComponentConstancy
open ErdosProblems.AntiRamseyCycleQuotientTriangleSplice

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- The original high-NEW hypotheses exclude three pairwise distinct
original host labels on a triangle in three distinct whole SAME-r selected
components. This is the literal raw triangle input of the component quotient. -/
theorem no_three_component_rainbow_triangle
    {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (u v w : Fin n) (huv : u ≠ v) (hvw : v ≠ w) (hwu : w ≠ u)
    (hUV : (selectedGraph χ r).connectedComponentMk u ≠
      (selectedGraph χ r).connectedComponentMk v)
    (hVW : (selectedGraph χ r).connectedComponentMk v ≠
      (selectedGraph χ r).connectedComponentMk w)
    (hWU : (selectedGraph χ r).connectedComponentMk w ≠
      (selectedGraph χ r).connectedComponentMk u) :
    ¬ (χ.get u v huv ≠ χ.get v w hvw ∧
      χ.get v w hvw ≠ χ.get w u hwu ∧
      χ.get w u hwu ≠ χ.get u v huv) := by
  let DA := (selectedGraph χ r).connectedComponentMk u
  let DB := (selectedGraph χ r).connectedComponentMk v
  let DD := (selectedGraph χ r).connectedComponentMk w
  have hu : u ∈ DA.supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ DB.supp := ConnectedComponent.connectedComponentMk_mem
  have hw : w ∈ DD.supp := ConnectedComponent.connectedComponentMk_mem
  obtain ⟨α, hα⟩ := cross_component_colors_constant hk χ r hnew hpair hno DA DB hUV
  obtain ⟨β, hβ⟩ := cross_component_colors_constant hk χ r hnew hpair hno DB DD hVW
  obtain ⟨γ, hγ⟩ := cross_component_colors_constant hk χ r hnew hpair hno DD DA hWU
  have hgetUV : χ.get u v huv = α := hα u v hu hv ⟨s(u, v), huv⟩ rfl
  have hgetVW : χ.get v w hvw = β := hβ v w hv hw ⟨s(v, w), hvw⟩ rfl
  have hgetWU : χ.get w u hwu = γ := hγ w u hw hu ⟨s(w, u), hwu⟩ rfl
  have hαOutside : α ∉ newColorUnion χ := by
    rw [← hgetUV]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DA DB hUV
      u v hu hv ⟨s(u, v), huv⟩ rfl
  have hβOutside : β ∉ newColorUnion χ := by
    rw [← hgetVW]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DB DD hVW
      v w hv hw ⟨s(v, w), hvw⟩ rfl
  have hγOutside : γ ∉ newColorUnion χ := by
    rw [← hgetWU]
    exact cross_edge_color_not_new_union hk χ r hnew hpair hno DD DA hWU
      w u hw hu ⟨s(w, u), hwu⟩ rfl
  obtain ⟨ha, haLower, haUpper, A, hA, _hontoA, hAspan, hAcycle, _hdegreeA,
      _hnewDegreeA⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DA
  obtain ⟨hb, hbLower, hbUpper, B, hB, _hontoB, hBspan, hBcycle, _hdegreeB,
      _hnewDegreeB⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DB
  obtain ⟨hc, hcLower, hcUpper, D, hD, _hontoD, hDspan, hDcycle, _hdegreeD,
      _hnewDegreeD⟩ := selected_component_cyclic_index hk χ r hnew hpair hno DD
  have hrepeat := three_components_cross_labels_repeat χ r hk ha hb hc
    haLower hbLower hcLower haUpper hbUpper hcUpper DA DB DD hUV hVW hWU
    A B D hA hB hD hAspan hBspan hDspan
    (fun i j hij => hAcycle hij) (fun i j hij => hBcycle hij)
    (fun i j hij => hDcycle hij) α β γ
    (fun x y e hx hy he => hα x y hx hy e he)
    (fun x y e hx hy he => hβ x y hx hy e he)
    (fun x y e hx hy he => hγ x y hx hy e he)
    hαOutside hβOutside hγOutside hno
  rintro ⟨hUVcolor, hVWcolor, hWUcolor⟩
  rcases hrepeat with hαβ | hβγ | hγα
  · exact hUVcolor (hgetUV.trans (hαβ.trans hgetVW.symm))
  · exact hVWcolor (hgetVW.trans (hβγ.trans hgetWU.symm))
  · exact hWUcolor (hgetWU.trans (hγα.trans hgetUV.symm))

end ErdosProblems.AntiRamseyCycleOriginalThreeComponentTriangle
