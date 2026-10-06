module

public import CycleSelectedNewEndpoint
public import CycleNewRepresentativeRainbow
public import CycleFourCopies
public import Mathlib.Tactic

@[expose] public section

/-!
At k=4, two outward selected edges whose colors are NEW at their inward
endpoints make an explicit rainbow host square unless they meet at one
third vertex. This is a semantic lemma for Choi's representing graph,
under the literal Formal Conjectures Copy and IsRainbow definitions.
-/

namespace ErdosProblems.AntiRamseyCycleFourNewWedge

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleSelectedNewEndpoint
open ErdosProblems.AntiRamseyCycleNewRepresentativeRainbow
open ErdosProblems.AntiRamseyCycleFour

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A selected edge, represented by its unordered endpoint pair. -/
def selectedPair (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) :
    (newColorRepresentative χ).edgeSet :=
  ⟨s(u, v), (SimpleGraph.mem_edgeSet _).mpr huv⟩

/-- The original host color of a selected edge. -/
def selectedEdgeColor (χ : TopEdgeLabeling (Fin n) C)
    {u v : Fin n} (huv : (newColorRepresentative χ).Adj u v) : C :=
  restrictedNewColor χ (selectedPair χ huv)

def squareMap (x u v y : Fin n) (i : Fin 4) : Fin n :=
  if i = 0 then x else if i = 1 then u else if i = 2 then v else y

theorem squareMap_injective {x u v y : Fin n}
    (hxu : x ≠ u) (hxv : x ≠ v) (hxy : x ≠ y)
    (huv : u ≠ v) (huy : u ≠ y) (hvy : v ≠ y) :
    Function.Injective (squareMap x u v y) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [squareMap] at hij ⊢ <;> grind

/-- A distinct fourth vertex makes the wedge into a literal rainbow
`cycleGraph 4.Copy` in the original complete-graph coloring. -/
theorem rainbow_square_of_selected_new_wedge
    (χ : TopEdgeLabeling (Fin n) C) {u v x y : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (hux : (newColorRepresentative χ).Adj u x)
    (hvy : (newColorRepresentative χ).Adj v y)
    (hxv : x ≠ v) (hyu : y ≠ u) (hxy : x ≠ y)
    (hnewUX : selectedEdgeColor χ hux ∈ newColors χ u)
    (hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v) :
    ∃ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      IsRainbow f.toHom χ := by
  have hxu : x ≠ u := (newColorRepresentative χ).ne_of_adj hux.symm
  have huv' : u ≠ v := (newColorRepresentative χ).ne_of_adj huv
  have huy : u ≠ y := hyu.symm
  have hvy' : v ≠ y := (newColorRepresentative χ).ne_of_adj hvy
  have hρ : Function.Injective (squareMap x u v y) :=
    squareMap_injective hxu hxv hxy huv' huy hvy'
  let φ : (cycleGraph 4) →g (⊤ : SimpleGraph (Fin n)) :=
    ⟨squareMap x u v y, by
      intro i j hij
      exact (top_adj _ _).mpr (hρ.ne ((cycleGraph 4).ne_of_adj hij))⟩
  let f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)) := ⟨φ, hρ⟩
  let closing : (⊤ : SimpleGraph (Fin n)).edgeSet :=
    ⟨s(y, x), (top_adj _ _).mpr hxy.symm⟩

  have h01_12 : selectedEdgeColor χ hux ≠ selectedEdgeColor χ huv := by
    intro hcol
    have he : selectedPair χ hux = selectedPair χ huv :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, x) = s(u, v) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind
  have h01_23 : selectedEdgeColor χ hux ≠ selectedEdgeColor χ hvy := by
    intro hcol
    have he : selectedPair χ hux = selectedPair χ hvy :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, x) = s(v, y) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind
  have h12_23 : selectedEdgeColor χ huv ≠ selectedEdgeColor χ hvy := by
    intro hcol
    have he : selectedPair χ huv = selectedPair χ hvy :=
      restrictedNewColor_injective χ hcol
    have hv := congrArg Subtype.val he
    change s(u, v) = s(v, y) at hv
    rcases (Sym2.eq_iff.mp hv) with hp | hp <;> grind

  have h01_30 : selectedEdgeColor χ hux ≠ χ closing := by
    intro hcol
    have huClosing : u ∈ closing.val :=
      newColor_every_edge_incident χ u hnewUX closing hcol.symm
    change u ∈ s(y, x) at huClosing
    rcases (Sym2.mem_iff.mp huClosing) with h | h <;> grind
  have h23_30 : selectedEdgeColor χ hvy ≠ χ closing := by
    intro hcol
    have hvClosing : v ∈ closing.val :=
      newColor_every_edge_incident χ v hnewVY closing hcol.symm
    change v ∈ s(y, x) at hvClosing
    rcases (Sym2.mem_iff.mp hvClosing) with h | h <;> grind
  have hdisj : ∀ z : Fin n, z ∈ (selectedPair χ huv).val →
      z ∉ closing.val := by
    intro z hz hzc
    change z ∈ s(u, v) at hz
    change z ∈ s(y, x) at hzc
    rcases (Sym2.mem_iff.mp hz) with h | h <;>
      rcases (Sym2.mem_iff.mp hzc) with h' | h' <;> grind
  have h12_30 : selectedEdgeColor χ huv ≠ χ closing := by
    exact selected_edge_color_ne_of_disjoint χ
      (selectedPair χ huv) closing hdisj

  have hcol01 : (EdgeLabeling.pullback χ f.toHom) sourceEdge01 =
      selectedEdgeColor χ hux := by
    change χ (f.toHom.mapEdgeSet sourceEdge01) =
      χ ⟨(selectedPair χ hux).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ hux).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((0 : Fin 4), 1)) = s(u, x)
    rw [Sym2.map_mk]
    simp [squareMap, Sym2.eq_swap]
  have hcol12 : (EdgeLabeling.pullback χ f.toHom) sourceEdge12 =
      selectedEdgeColor χ huv := by
    change χ (f.toHom.mapEdgeSet sourceEdge12) =
      χ ⟨(selectedPair χ huv).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ huv).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((1 : Fin 4), 2)) = s(u, v)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol23 : (EdgeLabeling.pullback χ f.toHom) sourceEdge23 =
      selectedEdgeColor χ hvy := by
    change χ (f.toHom.mapEdgeSet sourceEdge23) =
      χ ⟨(selectedPair χ hvy).val,
        SimpleGraph.edgeSet_mono le_top (selectedPair χ hvy).property⟩
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((2 : Fin 4), 3)) = s(v, y)
    rw [Sym2.map_mk]
    simp [squareMap]
  have hcol30 : (EdgeLabeling.pullback χ f.toHom) sourceEdge30 =
      χ closing := by
    change χ (f.toHom.mapEdgeSet sourceEdge30) = χ closing
    apply congrArg χ
    apply Subtype.ext
    change Sym2.map (squareMap x u v y) (s((3 : Fin 4), 0)) = s(y, x)
    rw [Sym2.map_mk]
    simp [squareMap]

  refine ⟨f, ?_⟩
  intro e₁ e₂ heq
  rcases sourceEdge_cases e₁ with h₁ | h₁ | h₁ | h₁ <;>
    rcases sourceEdge_cases e₂ with h₂ | h₂ | h₂ | h₂ <;>
    subst e₁ <;> subst e₂ <;>
    simp_all

/-- Under the original no-rainbow premise, the two NEW-outward selected
edges of a selected edge have the same third endpoint. -/
theorem selected_new_wedge_eq
    (χ : TopEdgeLabeling (Fin n) C)
    (hno : ∀ f : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    {u v x y : Fin n}
    (huv : (newColorRepresentative χ).Adj u v)
    (hux : (newColorRepresentative χ).Adj u x)
    (hvy : (newColorRepresentative χ).Adj v y)
    (hxv : x ≠ v) (hyu : y ≠ u)
    (hnewUX : selectedEdgeColor χ hux ∈ newColors χ u)
    (hnewVY : selectedEdgeColor χ hvy ∈ newColors χ v) :
    x = y := by
  by_contra hxy
  obtain ⟨f, hf⟩ := rainbow_square_of_selected_new_wedge χ
    huv hux hvy hxv hyu hxy hnewUX hnewVY
  exact hno f hf

end ErdosProblems.AntiRamseyCycleFourNewWedge
