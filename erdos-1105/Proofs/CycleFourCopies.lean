module

public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

/-! Three explicitly embedded four-cycles in the complete graph on Fin 4. -/

namespace ErdosProblems.AntiRamseyCycleFour

open SimpleGraph

def copyOfInjection (v : Fin 4 → Fin 4) (hv : Function.Injective v) :
    (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  ⟨⟨v, by
      intro i j hij
      exact (top_adj _ _).mpr (hv.ne ((cycleGraph 4).ne_of_adj hij))⟩, hv⟩

def mapZero : Fin 4 → Fin 4 := id
def mapOne : Fin 4 → Fin 4 := fun i =>
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 3 else 2
def mapTwo : Fin 4 → Fin 4 := fun i =>
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 1 else 3

theorem mapZero_injective : Function.Injective mapZero := by
  intro i j hij
  exact hij

theorem mapOne_injective : Function.Injective mapOne := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [mapOne] at hij ⊢

theorem mapTwo_injective : Function.Injective mapTwo := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [mapTwo] at hij ⊢

/- The image edges are respectively the three complements of perfect matchings. -/
def squareCopyZero : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapZero mapZero_injective

def squareCopyOne : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapOne mapOne_injective

def squareCopyTwo : (cycleGraph 4).Copy (⊤ : SimpleGraph (Fin 4)) :=
  copyOfInjection mapTwo mapTwo_injective

def sourceEdge01 : (cycleGraph 4).edgeSet :=
  ⟨s((0 : Fin 4), 1), by
    change ((0 : Fin 4) - 1 = 1 ∨ (1 : Fin 4) - 0 = 1)
    exact Or.inr rfl⟩

def sourceEdge12 : (cycleGraph 4).edgeSet :=
  ⟨s((1 : Fin 4), 2), by
    change ((1 : Fin 4) - 2 = 1 ∨ (2 : Fin 4) - 1 = 1)
    exact Or.inr rfl⟩

def sourceEdge23 : (cycleGraph 4).edgeSet :=
  ⟨s((2 : Fin 4), 3), by
    change ((2 : Fin 4) - 3 = 1 ∨ (3 : Fin 4) - 2 = 1)
    exact Or.inr rfl⟩

def sourceEdge30 : (cycleGraph 4).edgeSet :=
  ⟨s((3 : Fin 4), 0), by
    change ((3 : Fin 4) - 0 = 1 ∨ (0 : Fin 4) - 3 = 1)
    exact Or.inr rfl⟩

theorem sourceEdge_cases (e : (cycleGraph 4).edgeSet) :
    e = sourceEdge01 ∨ e = sourceEdge12 ∨
      e = sourceEdge23 ∨ e = sourceEdge30 := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    fin_cases i <;> fin_cases j <;> revert hq <;> decide

def targetEdge01 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 1), by
    change (0 : Fin 4) ≠ 1
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge02 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 2), by
    change (0 : Fin 4) ≠ 2
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge03 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((0 : Fin 4), 3), by
    change (0 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge12 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((1 : Fin 4), 2), by
    change (1 : Fin 4) ≠ 2
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge13 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((1 : Fin 4), 3), by
    change (1 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

def targetEdge23 : (⊤ : SimpleGraph (Fin 4)).edgeSet :=
  ⟨s((2 : Fin 4), 3), by
    change (2 : Fin 4) ≠ 3
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv⟩

theorem completeFourEdge_cases (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    e = targetEdge01 ∨ e = targetEdge02 ∨ e = targetEdge03 ∨
      e = targetEdge12 ∨ e = targetEdge13 ∨ e = targetEdge23 := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ i j =>
    fin_cases i <;> fin_cases j <;> revert hq <;> decide

theorem copyTwo_omits_edge01 (e : (cycleGraph 4).edgeSet) :
    squareCopyTwo.toHom.mapEdgeSet e ≠ targetEdge01 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyZero_omits_edge02 (e : (cycleGraph 4).edgeSet) :
    squareCopyZero.toHom.mapEdgeSet e ≠ targetEdge02 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyOne_omits_edge03 (e : (cycleGraph 4).edgeSet) :
    squareCopyOne.toHom.mapEdgeSet e ≠ targetEdge03 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyOne_omits_edge12 (e : (cycleGraph 4).edgeSet) :
    squareCopyOne.toHom.mapEdgeSet e ≠ targetEdge12 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyZero_omits_edge13 (e : (cycleGraph 4).edgeSet) :
    squareCopyZero.toHom.mapEdgeSet e ≠ targetEdge13 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem copyTwo_omits_edge23 (e : (cycleGraph 4).edgeSet) :
    squareCopyTwo.toHom.mapEdgeSet e ≠ targetEdge23 := by
  rcases sourceEdge_cases e with rfl | rfl | rfl | rfl <;> decide

theorem every_target_edge_omitted_by_a_square
    (e : (⊤ : SimpleGraph (Fin 4)).edgeSet) :
    (∀ x : (cycleGraph 4).edgeSet, squareCopyZero.toHom.mapEdgeSet x ≠ e) ∨
    (∀ x : (cycleGraph 4).edgeSet, squareCopyOne.toHom.mapEdgeSet x ≠ e) ∨
    (∀ x : (cycleGraph 4).edgeSet, squareCopyTwo.toHom.mapEdgeSet x ≠ e) := by
  rcases completeFourEdge_cases e with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr copyTwo_omits_edge01)
  · exact Or.inl copyZero_omits_edge02
  · exact Or.inr (Or.inl copyOne_omits_edge03)
  · exact Or.inr (Or.inl copyOne_omits_edge12)
  · exact Or.inl copyZero_omits_edge13
  · exact Or.inr (Or.inr copyTwo_omits_edge23)

end ErdosProblems.AntiRamseyCycleFour
