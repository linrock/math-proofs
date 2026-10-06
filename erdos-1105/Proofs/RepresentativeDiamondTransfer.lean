module

public import RepresentativeGraph
public import DiamondPathCopy

@[expose] public section

/-!
Five distinctly colored representative edges forming a diamond give a
rainbow `pathGraph 5` copy in the original complete-graph coloring. The
four diamond vertices can be supplemented by any fifth host vertex.
-/

namespace ErdosProblems.AntiRamseyPathFiveTransfer

open SimpleGraph
open ErdosProblems.AntiRamseyRepresentative
open ErdosProblems.AntiRamseyPathFiveUpper

/-- The five edges of a diamond on named vertices `a,b,c,d`. Its missing
edge `a-b` is unrestricted. -/
def DiamondOn {V : Type*} (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- The diamond edges `ac,ad,bc,bd,cd` at positions 0 through 4,
where the first index of `Fin 5` is reserved for the extra vertex. -/
def diamondIndex (i : Fin 5) : Sym2 (Fin 5) :=
  if i = 0 then s(1, 3)
  else if i = 1 then s(1, 4)
  else if i = 2 then s(2, 3)
  else if i = 3 then s(2, 4)
  else s(3, 4)

theorem diamondIndex_injective : Function.Injective diamondIndex := by
  decide

/-- The five edges inside a representative diamond as graph edge subtypes. -/
def representativeDiamondEdge {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) : (representativeGraph χ hχ).edgeSet :=
  if i = 0 then ⟨s(u 1, u 3), hd.1⟩
  else if i = 1 then ⟨s(u 1, u 4), hd.2.1⟩
  else if i = 2 then ⟨s(u 2, u 3), hd.2.2.1⟩
  else if i = 3 then ⟨s(u 2, u 4), hd.2.2.2.1⟩
  else ⟨s(u 3, u 4), hd.2.2.2.2⟩

theorem representativeDiamondEdge_val {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) :
    (representativeDiamondEdge χ hχ u hd i).val =
      Sym2.map u (diamondIndex i) := by
  fin_cases i <;>
    simp [representativeDiamondEdge, diamondIndex, Sym2.map_mk]

theorem representativeDiamondEdge_injective {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4)) :
    Function.Injective (representativeDiamondEdge χ hχ u hd) := by
  intro i j he
  apply diamondIndex_injective
  apply Sym2.map.injective hu
  calc
    Sym2.map u (diamondIndex i) =
        (representativeDiamondEdge χ hχ u hd i).val :=
      (representativeDiamondEdge_val χ hχ u hd i).symm
    _ = (representativeDiamondEdge χ hχ u hd j).val := congrArg Subtype.val he
    _ = Sym2.map u (diamondIndex j) :=
      representativeDiamondEdge_val χ hχ u hd j

theorem diamondEdgeColors_eq_restrictedColor {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4))
    (i : Fin 5) :
    diamondEdgeColors χ u hu i =
      restrictedColor χ hχ (representativeDiamondEdge χ hχ u hd i) := by
  fin_cases i <;>
    simp [diamondEdgeColors, representativeDiamondEdge, restrictedColor,
      EdgeLabeling.get]

/-- A five-vertex embedding whose four diamond vertices have five edges in
the one-edge-per-color representative graph yields a rainbow `P₅` copy. -/
theorem rainbow_path_five_of_representative_diamond_five {n q : ℕ}
    (χ : TopEdgeLabeling (Fin n) (Fin q)) (hχ : Function.Surjective χ)
    (u : Fin 5 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 1) (u 2) (u 3) (u 4)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hcolors : Function.Injective (diamondEdgeColors χ u hu) := by
    intro i j he
    apply representativeDiamondEdge_injective χ hχ u hu hd
    apply restrictedColor_injective χ hχ
    exact (diamondEdgeColors_eq_restrictedColor χ hχ u hu hd i).symm.trans
      (he.trans (diamondEdgeColors_eq_restrictedColor χ hχ u hu hd j))
  exact rainbow_path_five_of_rainbow_diamond χ u hu hcolors

/-- Four representative diamond vertices can be supplemented by a fifth
vertex when the host has at least five vertices. -/
theorem rainbow_path_five_of_representative_diamond_four {n q : ℕ}
    (hn : 5 ≤ n) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (u : Fin 4 → Fin n) (hu : Function.Injective u)
    (hd : DiamondOn (representativeGraph χ hχ) (u 0) (u 1) (u 2) (u 3)) :
    ∃ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)), IsRainbow f.toHom χ := by
  have hnot_surj : ¬Function.Surjective u := by
    intro hs
    have hcard : 4 = n := by
      simpa using Fintype.card_congr (Equiv.ofBijective u ⟨hu, hs⟩)
    omega
  obtain ⟨v, hv⟩ : ∃ v : Fin n, ∀ i : Fin 4, u i ≠ v := by
    by_contra h
    push Not at h
    apply hnot_surj
    intro v
    obtain ⟨i, hi⟩ := h v
    exact ⟨i, by simpa using hi⟩
  have hv_not_range : v ∉ Set.range u := by
    rintro ⟨i, hi⟩
    exact hv i hi
  let w : Fin 5 → Fin n := Fin.cons v u
  have hw : Function.Injective w :=
    Fin.cons_injective_of_injective hv_not_range hu
  have hw₁ : w 1 = u 0 := by
    change w (Fin.succ (0 : Fin 4)) = u 0
    simp only [w, Fin.cons_succ]
  have hw₂ : w 2 = u 1 := by
    change w (Fin.succ (1 : Fin 4)) = u 1
    simp only [w, Fin.cons_succ]
  have hw₃ : w 3 = u 2 := by
    change w (Fin.succ (2 : Fin 4)) = u 2
    simp only [w, Fin.cons_succ]
  have hw₄ : w 4 = u 3 := by
    change w (Fin.succ (3 : Fin 4)) = u 3
    simp only [w, Fin.cons_succ]
  have hdiamond :
      DiamondOn (representativeGraph χ hχ) (w 1) (w 2) (w 3) (w 4) := by
    simpa only [hw₁, hw₂, hw₃, hw₄] using hd
  exact rainbow_path_five_of_representative_diamond_five χ hχ w hw hdiamond

/-- A coloring with no rainbow five-vertex path has no injectively embedded
diamond among its representative edges, for every `n ≥ 5`. -/
theorem no_representative_diamond_of_no_rainbow_path_five {n q : ℕ}
    (hn : 5 ≤ n) (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ)
    (hno : ∀ f : (pathGraph 5).Copy (⊤ : SimpleGraph (Fin n)),
      ¬IsRainbow f.toHom χ)
    (u : Fin 4 → Fin n) (hu : Function.Injective u) :
    ¬DiamondOn (representativeGraph χ hχ) (u 0) (u 1) (u 2) (u 3) := by
  intro hd
  obtain ⟨f, hf⟩ := rainbow_path_five_of_representative_diamond_four hn χ hχ u hu hd
  exact hno f hf

end ErdosProblems.AntiRamseyPathFiveTransfer
