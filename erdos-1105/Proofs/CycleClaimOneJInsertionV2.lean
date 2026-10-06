module

public import CycleClaimOneSecondInsertionV2
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-!
Choi Claim 1 Case B. The two-spoke candidate
is not imported. This module constructs no full Case B or weak-block theorem.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneJInsertion

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleOrderedEdges
open ErdosProblems.AntiRamseyCycleClaimOneFirstInsertion
open ErdosProblems.AntiRamseyCycleClaimOneSecondInsertion

variable {n : ℕ} {C : Type*} [DecidableEq C]

def betweenEdge (x y : Fin n) (hxy : x ≠ y) : HostEdge n :=
  ⟨s(x, y), (top_adj _ _).mpr hxy⟩

/-- Retained source order `m-1,0,...,m-2`; the last cycle vertex is omitted. -/
def leftBase (m : ℕ) : Fin m ↪ Fin (m + 1) where
  toFun j := Fin.castSucc ((finRotate m).symm j)
  inj' := (Fin.castSucc_injective m).comp (finRotate m).symm.injective

/-- Retained source order `0,2,...,m`; source vertex one is omitted. -/
def rightBase (m : ℕ) : Fin m ↪ Fin (m + 1) :=
  (Fin.succAboveOrderEmb (1 : Fin (m + 1))).toEmbedding

def retainedPosition {m : ℕ} (hm : 2 ≤ m)
    (i : Fin (m + 2)) : Fin m := ⟨i.val - 2, by omega⟩

def slotMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n) (i : Fin (m + 2)) : Fin n :=
  if i.val = 1 then x else if i.val = 2 then y
  else cyc.toHom (ρ (retainedPosition hm i))

theorem slotMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : slotMap hm cyc ρ x y i = x := by
  simp only [slotMap, ite_eq_left hi]

theorem slotMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi1 : i.val ≠ 1) (hi2 : i.val = 2) :
    slotMap hm cyc ρ x y i = y := by
  simp only [slotMap, ite_eq_right hi1, ite_eq_left hi2]

theorem slotMap_other {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (i : Fin (m + 2)) (hi1 : i.val ≠ 1) (hi2 : i.val ≠ 2) :
    slotMap hm cyc ρ x y i = cyc.toHom (ρ (retainedPosition hm i)) := by
  simp only [slotMap, ite_eq_right hi1, ite_eq_right hi2]

theorem slotMap_injective {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (ρ : Fin m ↪ Fin (m + 1)) (x y : Fin n)
    (hx : x ∉ Set.range cyc.toHom) (hy : y ∉ Set.range cyc.toHom)
    (hxy : x ≠ y) : Function.Injective (slotMap hm cyc ρ x y) := by
  intro a b hab
  by_cases ha1 : a.val = 1
  · by_cases hb1 : b.val = 1
    · exact Fin.ext (ha1.trans hb1.symm)
    by_cases hb2 : b.val = 2
    · rw [slotMap_one hm cyc ρ x y a ha1,
        slotMap_two hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hxy hab)
    · rw [slotMap_one hm cyc ρ x y a ha1,
        slotMap_other hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hx ⟨ρ (retainedPosition hm b), hab.symm⟩)
  by_cases ha2 : a.val = 2
  · by_cases hb1 : b.val = 1
    · rw [slotMap_two hm cyc ρ x y a ha1 ha2,
        slotMap_one hm cyc ρ x y b hb1] at hab
      exact False.elim (hxy hab.symm)
    by_cases hb2 : b.val = 2
    · exact Fin.ext (ha2.trans hb2.symm)
    · rw [slotMap_two hm cyc ρ x y a ha1 ha2,
        slotMap_other hm cyc ρ x y b hb1 hb2] at hab
      exact False.elim (hy ⟨ρ (retainedPosition hm b), hab.symm⟩)
  by_cases hb1 : b.val = 1
  · rw [slotMap_other hm cyc ρ x y a ha1 ha2,
      slotMap_one hm cyc ρ x y b hb1] at hab
    exact False.elim (hx ⟨ρ (retainedPosition hm a), hab⟩)
  by_cases hb2 : b.val = 2
  · rw [slotMap_other hm cyc ρ x y a ha1 ha2,
      slotMap_two hm cyc ρ x y b hb1 hb2] at hab
    exact False.elim (hy ⟨ρ (retainedPosition hm a), hab⟩)
  rw [slotMap_other hm cyc ρ x y a ha1 ha2,
    slotMap_other hm cyc ρ x y b hb1 hb2] at hab
  have hidx := ρ.injective (cyc.injective hab)
  have hval := congrArg Fin.val hidx
  change a.val - 2 = b.val - 2 at hval
  apply Fin.ext
  omega

theorem leftBase_zero {m : ℕ} (hm : 2 ≤ m) :
    leftBase m (⟨0, by omega⟩ : Fin m) =
      (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
  cases m with
  | zero => omega
  | succ k =>
      apply Fin.ext
      change ((finRotate (k + 1)).symm (0 : Fin (k + 1))).val = (k + 1) - 1
      simp only [finRotate_symm_apply, Fin.coe_sub_one, ite_true,
        Nat.add_sub_cancel]

theorem leftBase_pos {m : ℕ} (hm : 2 ≤ m) (j : Fin m)
    (hj : 1 ≤ j.val) :
    leftBase m j = (⟨j.val - 1, by omega⟩ : Fin (m + 1)) := by
  have hj0 : j ≠ (⟨0, by omega⟩ : Fin m) := by
    intro h
    have hval := congrArg Fin.val h
    change j.val = 0 at hval
    omega
  apply Fin.ext
  change ((finRotate m).symm j).val = j.val - 1
  rw [finRotate_symm_apply, Fin.val_sub_one_of_ne_zero hj0]

theorem rightBase_zero {m : ℕ} (hm : 2 ≤ m) :
    rightBase m (⟨0, by omega⟩ : Fin m) = (0 : Fin (m + 1)) := by
  cases m with
  | zero => omega
  | succ k =>
      change (1 : Fin (k + 2)).succAbove (0 : Fin (k + 1)) = 0
      exact Fin.one_succAbove_zero

theorem rightBase_pos {m : ℕ} (hm : 2 ≤ m) (j : Fin m)
    (hj : 1 ≤ j.val) :
    rightBase m j = (⟨j.val + 1, by omega⟩ : Fin (m + 1)) := by
  have hone : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one' (m + 1), Nat.mod_eq_of_lt (by omega)]
  have hle : (1 : Fin (m + 1)) ≤ Fin.castSucc j := by
    change ((1 : Fin (m + 1)) : ℕ) ≤ (Fin.castSucc j).val
    simpa only [hone, Fin.val_castSucc] using hj
  change (1 : Fin (m + 1)).succAbove j = ⟨j.val + 1, by omega⟩
  exact Fin.succAbove_of_le_castSucc _ _ hle

def jLeftMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Fin (m + 2) → Fin n := slotMap hm cyc (leftBase m) u w

def jRightMap {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Fin (m + 2) → Fin n := slotMap hm cyc (rightBase m) w u

theorem jLeftMap_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    jLeftMap hm cyc u w 0 = cyc.toHom ⟨m - 1, by omega⟩ := by
  change slotMap hm cyc (leftBase m) u w 0 = _
  rw [slotMap_other hm cyc (leftBase m) u w 0 (by exact Nat.zero_ne_one)
    (by exact Nat.zero_ne_add_one 1)]
  exact congrArg cyc.toHom (leftBase_zero hm)

theorem jRightMap_zero {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    jRightMap hm cyc u w 0 = cyc.toHom 0 := by
  change slotMap hm cyc (rightBase m) w u 0 = _
  rw [slotMap_other hm cyc (rightBase m) w u 0 (by exact Nat.zero_ne_one)
    (by exact Nat.zero_ne_add_one 1)]
  exact congrArg cyc.toHom (rightBase_zero hm)

theorem jLeftMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : jLeftMap hm cyc u w i = u :=
  slotMap_one hm cyc (leftBase m) u w i hi

theorem jLeftMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 2) : jLeftMap hm cyc u w i = w :=
  slotMap_two hm cyc (leftBase m) u w i (by omega) hi

theorem jRightMap_one {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 1) : jRightMap hm cyc u w i = w :=
  slotMap_one hm cyc (rightBase m) w u i hi

theorem jRightMap_two {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : i.val = 2) : jRightMap hm cyc u w i = u :=
  slotMap_two hm cyc (rightBase m) w u i (by omega) hi

theorem jLeftMap_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : 3 ≤ i.val) :
    jLeftMap hm cyc u w i = cyc.toHom ⟨i.val - 3, by omega⟩ := by
  change slotMap hm cyc (leftBase m) u w i = _
  rw [slotMap_other hm cyc (leftBase m) u w i (by omega) (by omega)]
  rw [leftBase_pos hm (retainedPosition hm i) (by dsimp [retainedPosition]; omega)]
  congr 1

theorem jRightMap_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 2)) (hi : 3 ≤ i.val) :
    jRightMap hm cyc u w i = cyc.toHom ⟨i.val - 1, by omega⟩ := by
  change slotMap hm cyc (rightBase m) w u i = _
  rw [slotMap_other hm cyc (rightBase m) w u i (by omega) (by omega)]
  rw [rightBase_pos hm (retainedPosition hm i) (by dsimp [retainedPosition]; omega)]
  congr 1
  apply Fin.ext
  dsimp [retainedPosition]
  omega

noncomputable def jLeftCopy {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)) := by
  have hp : Function.Injective (jLeftMap hm cyc u w) :=
    slotMap_injective hm cyc (leftBase m) u w hu hw huw
  exact ⟨⟨jLeftMap hm cyc u w, by
    intro a b hab
    exact (top_adj _ _).mpr (hp.ne ((cycleGraph (m + 2)).ne_of_adj hab))⟩, hp⟩

noncomputable def jRightCopy {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)) := by
  have hp : Function.Injective (jRightMap hm cyc u w) :=
    slotMap_injective hm cyc (rightBase m) w u hw hu huw.symm
  exact ⟨⟨jRightMap hm cyc u w, by
    intro a b hab
    exact (top_adj _ _).mpr (hp.ne ((cycleGraph (m + 2)).ne_of_adj hab))⟩, hp⟩

theorem jLeftMap_step_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 1)) (hi : 3 ≤ i.val) :
    ∃ j : Fin m, j.val + 1 < m ∧
      Sym2.map (jLeftMap hm cyc u w) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 3, by omega⟩
  have hj : j.val + 1 < m := by dsimp [j]; omega
  have hlo := jLeftMap_tail hm cyc u w (Fin.castSucc i)
    (by simpa only [Fin.val_castSucc] using hi)
  have hhi := jLeftMap_tail hm cyc u w (Fin.succ i)
    (by simp only [Fin.val_succ]; omega)
  have hloIndex : (⟨(Fin.castSucc i).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc j := by
    apply Fin.ext
    rfl
  have hhiIndex : (⟨(Fin.succ i).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.succ j := by
    apply Fin.ext
    dsimp [j]
    omega
  refine ⟨j, hj, ?_⟩
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi, hloIndex, hhiIndex]

theorem jRightMap_step_tail {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (i : Fin (m + 1)) (hi : 3 ≤ i.val) :
    ∃ j : Fin m, 2 ≤ j.val ∧
      Sym2.map (jRightMap hm cyc u w) (sourceStep i).val =
        Sym2.map cyc.toHom (sourceStep j).val := by
  let j : Fin m := ⟨i.val - 1, by omega⟩
  have hj : 2 ≤ j.val := by dsimp [j]; omega
  have hlo := jRightMap_tail hm cyc u w (Fin.castSucc i)
    (by simpa only [Fin.val_castSucc] using hi)
  have hhi := jRightMap_tail hm cyc u w (Fin.succ i)
    (by simp only [Fin.val_succ]; omega)
  have hloIndex : (⟨(Fin.castSucc i).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc j := by
    apply Fin.ext
    rfl
  have hhiIndex : (⟨(Fin.succ i).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.succ j := by
    apply Fin.ext
    dsimp [j]
    omega
  refine ⟨j, hj, ?_⟩
  simp only [sourceStep, Sym2.map_mk]
  rw [hlo, hhi, hloIndex, hhiIndex]

theorem jLeftMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Sym2.map (jLeftMap hm cyc u w) (sourceClosing (m + 1) (by omega)).val =
      Sym2.map cyc.toHom (sourceStep (⟨m - 2, by omega⟩ : Fin m)).val := by
  have hlast := jLeftMap_tail hm cyc u w (Fin.last (m + 1))
    (by simp only [Fin.val_last]; omega)
  simp only [sourceClosing, sourceStep, Sym2.map_mk]
  rw [jLeftMap_zero hm cyc u w, hlast]
  have h0 : (⟨m - 1, by omega⟩ : Fin (m + 1)) =
      Fin.succ (⟨m - 2, by omega⟩ : Fin m) := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hlast0 : (⟨(Fin.last (m + 1)).val - 3, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨m - 2, by omega⟩ : Fin m) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_castSucc]
    omega
  rw [h0, hlast0]
  exact Sym2.eq_swap

theorem jRightMap_closing {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n) :
    Sym2.map (jRightMap hm cyc u w) (sourceClosing (m + 1) (by omega)).val =
      Sym2.map cyc.toHom (sourceClosing m hm).val := by
  have hlast := jRightMap_tail hm cyc u w (Fin.last (m + 1))
    (by simp only [Fin.val_last]; omega)
  have hlastIndex : (⟨(Fin.last (m + 1)).val - 1, by omega⟩ : Fin (m + 1)) =
      Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  simp only [sourceClosing, Sym2.map_mk]
  rw [jRightMap_zero hm cyc u w, hlast, hlastIndex]

def ThreeEdgeClass {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (Retained : (cycleGraph (m + 1)).edgeSet → Prop)
    (e₀ e₁ e₂ : (cycleGraph (m + 2)).edgeSet)
    (α β γ : C) (e : (cycleGraph (m + 2)).edgeSet) : Prop :=
  (e = e₀ ∧ EdgeLabeling.pullback χ f.toHom e = α) ∨
  (e = e₁ ∧ EdgeLabeling.pullback χ f.toHom e = β) ∨
  (e = e₂ ∧ EdgeLabeling.pullback χ f.toHom e = γ) ∨
  ∃ d : (cycleGraph (m + 1)).edgeSet,
    Retained d ∧
    EdgeLabeling.pullback χ f.toHom e = restrictedColor χ r (cyc.mapEdgeSet d) ∧
    f.mapEdgeSet e =
      (⟨(cyc.mapEdgeSet d).val,
        SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩ : HostEdge n)

/-- Retained edges keep their actual host-edge map equality. -/
theorem three_inserted_palette_isRainbow {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (Retained : (cycleGraph (m + 1)).edgeSet → Prop)
    (e₀ e₁ e₂ : (cycleGraph (m + 2)).edgeSet)
    (α β γ : C)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hAvoid : ∀ d : (cycleGraph (m + 1)).edgeSet, Retained d →
      α ≠ restrictedColor χ r (cyc.mapEdgeSet d) ∧
      β ≠ restrictedColor χ r (cyc.mapEdgeSet d) ∧
      γ ≠ restrictedColor χ r (cyc.mapEdgeSet d))
    (hClass : ∀ e : (cycleGraph (m + 2)).edgeSet,
      (e = e₀ ∧ EdgeLabeling.pullback χ f.toHom e = α) ∨
      (e = e₁ ∧ EdgeLabeling.pullback χ f.toHom e = β) ∨
      (e = e₂ ∧ EdgeLabeling.pullback χ f.toHom e = γ) ∨
      ∃ d : (cycleGraph (m + 1)).edgeSet,
        Retained d ∧
        EdgeLabeling.pullback χ f.toHom e =
          restrictedColor χ r (cyc.mapEdgeSet d) ∧
        f.mapEdgeSet e =
          (⟨(cyc.mapEdgeSet d).val,
            SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩ :
              HostEdge n)) : IsRainbow f.toHom χ := by
  let L := EdgeLabeling.pullback χ f.toHom
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  change Function.Injective L
  intro a b heq
  rcases hClass a with hA₁ | hB₁ | hC₁ | hR₁
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact hA₁.1.trans hA₂.1.symm
    · exact False.elim (hαβ (hA₁.2.symm.trans (heq.trans hB₂.2)))
    · exact False.elim (hαγ (hA₁.2.symm.trans (heq.trans hC₂.2)))
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).1 (hA₁.2.symm.trans (heq.trans hc)))
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim (hαβ (hA₂.2.symm.trans (heq.symm.trans hB₁.2)))
    · exact hB₁.1.trans hB₂.1.symm
    · exact False.elim (hβγ (hB₁.2.symm.trans (heq.trans hC₂.2)))
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).2.1 (hB₁.2.symm.trans (heq.trans hc)))
  · rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim (hαγ (hA₂.2.symm.trans (heq.symm.trans hC₁.2)))
    · exact False.elim (hβγ (hB₂.2.symm.trans (heq.symm.trans hC₁.2)))
    · exact hC₁.1.trans hC₂.1.symm
    · obtain ⟨d, hd, hc, _⟩ := hR₂
      exact False.elim ((hAvoid d hd).2.2 (hC₁.2.symm.trans (heq.trans hc)))
  · obtain ⟨d₁, hd₁, hc₁, hm₁⟩ := hR₁
    rcases hClass b with hA₂ | hB₂ | hC₂ | hR₂
    · exact False.elim ((hAvoid d₁ hd₁).1 (hA₂.2.symm.trans (heq.symm.trans hc₁)))
    · exact False.elim ((hAvoid d₁ hd₁).2.1 (hB₂.2.symm.trans (heq.symm.trans hc₁)))
    · exact False.elim ((hAvoid d₁ hd₁).2.2 (hC₂.2.symm.trans (heq.symm.trans hc₁)))
    · obtain ⟨d₂, _, hc₂, hm₂⟩ := hR₂
      have hcolors := hc₁.symm.trans (heq.trans hc₂)
      have hd : d₁ = d₂ :=
        cyc.mapEdgeSet.injective (restrictedColor_injective χ r hcolors)
      apply f.mapEdgeSet.injective
      exact hm₁.trans ((congrArg lifted hd).trans hm₂.symm)

def RetainedLeft {m : ℕ} (d : (cycleGraph (m + 1)).edgeSet) : Prop :=
  ∃ j : Fin m, j.val + 1 < m ∧ d = sourceStep j

def RetainedRight {m : ℕ} (hm : 2 ≤ m)
    (d : (cycleGraph (m + 1)).edgeSet) : Prop :=
  (∃ j : Fin m, 2 ≤ j.val ∧ d = sourceStep j) ∨ d = sourceClosing m hm

omit [DecidableEq C] in
theorem copy_color_of_map {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C)
    (f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)))
    (e : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
    (hmap : f.mapEdgeSet e = d) :
    EdgeLabeling.pullback χ f.toHom e = χ d := by
  simpa only [EdgeLabeling.pullback_apply, SimpleGraph.Copy.mapEdgeSet,
    Function.Embedding.coeFn_mk]
    using congrArg χ hmap

theorem jLeftMap_first_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc u hu (⟨m - 1, by omega⟩ : Fin (m + 1))).val := by
  change s(jLeftMap hm cyc u w 0,
    jLeftMap hm cyc u w (Fin.succ (⟨0, by omega⟩ : Fin (m + 1)))) =
      s(u, cyc.toHom ⟨m - 1, by omega⟩)
  rw [jLeftMap_zero hm cyc u w,
    jLeftMap_one hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jLeftMap_bridge {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (huw : u ≠ w) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))).val =
      (betweenEdge u w huw).val := by
  change s(jLeftMap hm cyc u w (Fin.castSucc (⟨1, by omega⟩ : Fin (m + 1))),
    jLeftMap hm cyc u w (Fin.succ (⟨1, by omega⟩ : Fin (m + 1)))) = s(u, w)
  rw [jLeftMap_one hm cyc u w _ rfl, jLeftMap_two hm cyc u w _ rfl]

theorem jLeftMap_third_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hw : w ∉ Set.range cyc.toHom) :
    Sym2.map (jLeftMap hm cyc u w)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc w hw 0).val := by
  change s(jLeftMap hm cyc u w (Fin.castSucc (⟨2, by omega⟩ : Fin (m + 1))),
    jLeftMap hm cyc u w (Fin.succ (⟨2, by omega⟩ : Fin (m + 1)))) =
      s(w, cyc.toHom 0)
  rw [jLeftMap_two hm cyc u w _ rfl, jLeftMap_tail hm cyc u w _ (by exact le_rfl)]
  rfl

theorem jRightMap_first_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hw : w ∉ Set.range cyc.toHom) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc w hw 0).val := by
  change s(jRightMap hm cyc u w 0,
    jRightMap hm cyc u w (Fin.succ (⟨0, by omega⟩ : Fin (m + 1)))) =
      s(w, cyc.toHom 0)
  rw [jRightMap_zero hm cyc u w, jRightMap_one hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jRightMap_bridge {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (huw : u ≠ w) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))).val =
      (betweenEdge u w huw).val := by
  change s(jRightMap hm cyc u w (Fin.castSucc (⟨1, by omega⟩ : Fin (m + 1))),
    jRightMap hm cyc u w (Fin.succ (⟨1, by omega⟩ : Fin (m + 1)))) = s(u, w)
  rw [jRightMap_one hm cyc u w _ rfl, jRightMap_two hm cyc u w _ rfl]
  exact Sym2.eq_swap

theorem jRightMap_third_spoke {m : ℕ} (hm : 2 ≤ m)
    {χ : TopEdgeLabeling (Fin n) C} {r : NewChoice χ}
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) :
    Sym2.map (jRightMap hm cyc u w)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))).val =
      (outsiderEdge cyc u hu (⟨2, by omega⟩ : Fin (m + 1))).val := by
  change s(jRightMap hm cyc u w (Fin.castSucc (⟨2, by omega⟩ : Fin (m + 1))),
    jRightMap hm cyc u w (Fin.succ (⟨2, by omega⟩ : Fin (m + 1)))) =
      s(u, cyc.toHom ⟨2, by omega⟩)
  rw [jRightMap_two hm cyc u w _ rfl, jRightMap_tail hm cyc u w _ (by exact le_rfl)]
  rfl

theorem jLeft_edge_classes {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (e : (cycleGraph (m + 2)).edgeSet) :
    ThreeEdgeClass χ r cyc (jLeftCopy hm cyc u w hu hw huw) RetainedLeft
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
      α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0)) e := by
  let f := jLeftCopy hm cyc u w hu hw huw
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (a : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
      (hval : Sym2.map (jLeftMap hm cyc u w) a.val = d.val) :
      f.mapEdgeSet a = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map (jLeftMap hm cyc u w) a.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet a = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet) (hmap : f.mapEdgeSet a = lifted d) :
      EdgeLabeling.pullback χ f.toHom a =
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [lifted, restrictedColor] using copy_color_of_map χ f a (lifted d) hmap
  have h0 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))) = α := by
    have hc := copy_color_of_map χ f _ _
      (hmapHost _ _ (jLeftMap_first_spoke hm cyc u w hu))
    exact hc.trans (hcommon ⟨m - 1, by omega⟩)
  have h1 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))) = χ (betweenEdge u w huw) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jLeftMap_bridge hm cyc u w huw))
  have h2 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))) = χ (outsiderEdge cyc w hw 0) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jLeftMap_third_spoke hm cyc u w hw))
  unfold ThreeEdgeClass
  rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
  · subst e
    by_cases hi0 : i.val = 0
    · have hidx : i = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hi0
      rw [hidx]
      exact Or.inl ⟨rfl, h0⟩
    by_cases hi1 : i.val = 1
    · have hidx : i = (⟨1, by omega⟩ : Fin (m + 1)) := Fin.ext hi1
      rw [hidx]
      exact Or.inr (Or.inl ⟨rfl, h1⟩)
    by_cases hi2 : i.val = 2
    · have hidx : i = (⟨2, by omega⟩ : Fin (m + 1)) := Fin.ext hi2
      rw [hidx]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h2⟩))
    have hi : 3 ≤ i.val := by omega
    obtain ⟨j, hj, hval⟩ := jLeftMap_step_tail hm cyc u w i hi
    have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))
  · subst e
    let j : Fin m := ⟨m - 2, by omega⟩
    have hj : j.val + 1 < m := by dsimp [j]; omega
    have hmap := hmapSelected _ _ (jLeftMap_closing hm cyc u w)
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))

theorem jRight_edge_classes {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (e : (cycleGraph (m + 2)).edgeSet) :
    ThreeEdgeClass χ r cyc (jRightCopy hm cyc u w hu hw huw) (RetainedRight hm)
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
      α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0)) e := by
  let f := jRightCopy hm cyc u w hu hw huw
  let lifted : (cycleGraph (m + 1)).edgeSet → HostEdge n := fun d =>
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  have hmapHost (a : (cycleGraph (m + 2)).edgeSet) (d : HostEdge n)
      (hval : Sym2.map (jRightMap hm cyc u w) a.val = d.val) :
      f.mapEdgeSet a = d := by
    apply Subtype.ext
    exact hval
  have hmapSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet)
      (hval : Sym2.map (jRightMap hm cyc u w) a.val = Sym2.map cyc.toHom d.val) :
      f.mapEdgeSet a = lifted d := by
    apply Subtype.ext
    exact hval
  have hcolorSelected (a : (cycleGraph (m + 2)).edgeSet)
      (d : (cycleGraph (m + 1)).edgeSet) (hmap : f.mapEdgeSet a = lifted d) :
      EdgeLabeling.pullback χ f.toHom a =
        restrictedColor χ r (cyc.mapEdgeSet d) := by
    simpa only [lifted, restrictedColor] using copy_color_of_map χ f a (lifted d) hmap
  have h0 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨0, by omega⟩ : Fin (m + 1))) = χ (outsiderEdge cyc w hw 0) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jRightMap_first_spoke hm cyc u w hw))
  have h1 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨1, by omega⟩ : Fin (m + 1))) = χ (betweenEdge u w huw) :=
    copy_color_of_map χ f _ _ (hmapHost _ _ (jRightMap_bridge hm cyc u w huw))
  have h2 : EdgeLabeling.pullback χ f.toHom
      (sourceStep (⟨2, by omega⟩ : Fin (m + 1))) = α := by
    have hc := copy_color_of_map χ f _ _
      (hmapHost _ _ (jRightMap_third_spoke hm cyc u w hu))
    exact hc.trans (hcommon ⟨2, by omega⟩)
  unfold ThreeEdgeClass
  rcases sourceEdge_cases (m := m + 1) (by omega) e with ⟨i, he⟩ | he
  · subst e
    by_cases hi0 : i.val = 0
    · have hidx : i = (⟨0, by omega⟩ : Fin (m + 1)) := Fin.ext hi0
      rw [hidx]
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h0⟩))
    by_cases hi1 : i.val = 1
    · have hidx : i = (⟨1, by omega⟩ : Fin (m + 1)) := Fin.ext hi1
      rw [hidx]
      exact Or.inr (Or.inl ⟨rfl, h1⟩)
    by_cases hi2 : i.val = 2
    · have hidx : i = (⟨2, by omega⟩ : Fin (m + 1)) := Fin.ext hi2
      rw [hidx]
      exact Or.inl ⟨rfl, h2⟩
    have hi : 3 ≤ i.val := by omega
    obtain ⟨j, hj, hval⟩ := jRightMap_step_tail hm cyc u w i hi
    have hmap := hmapSelected (sourceStep i) (sourceStep j) hval
    exact Or.inr (Or.inr (Or.inr ⟨sourceStep j, Or.inl ⟨j, hj, rfl⟩,
      hcolorSelected _ _ hmap, hmap⟩))
  · subst e
    have hmap := hmapSelected _ _ (jRightMap_closing hm cyc u w)
    exact Or.inr (Or.inr (Or.inr ⟨sourceClosing m hm, Or.inr rfl,
      hcolorSelected _ _ hmap, hmap⟩))

theorem outside_not_selected_cycle_edge {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (d : (cycleGraph (m + 1)).edgeSet) : u ∉ (cyc.mapEdgeSet d).val := by
  intro he
  change u ∈ Sym2.map cyc.toHom d.val at he
  obtain ⟨i, _, hi⟩ := Sym2.mem_map.mp he
  exact hu ⟨i, hi⟩

theorem new_color_ne_edge_of_not_mem
    (χ : TopEdgeLabeling (Fin n) C) (u : Fin n) (α : C)
    (hαnew : α ∈ newColors χ u) (e : HostEdge n) (hu : u ∉ e.val) : α ≠ χ e := by
  intro heq
  exact hu (newColor_every_edge_incident χ u hαnew e heq.symm)

theorem outside_new_ne_selected_cycle_color {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (α : C) (hαnew : α ∈ newColors χ u)
    (d : (cycleGraph (m + 1)).edgeSet) :
    α ≠ restrictedColor χ r (cyc.mapEdgeSet d) := by
  let e : HostEdge n :=
    ⟨(cyc.mapEdgeSet d).val,
      SimpleGraph.edgeSet_mono le_top (cyc.mapEdgeSet d).property⟩
  exact new_color_ne_edge_of_not_mem χ u α hαnew e
    (outside_not_selected_cycle_edge χ r cyc u hu d)

theorem outside_not_gamma_edge {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (u w : Fin n) (hu : u ∉ Set.range cyc.toHom)
    (hw : w ∉ Set.range cyc.toHom) (huw : u ≠ w) :
    u ∉ (outsiderEdge cyc w hw 0).val := by
  intro he
  have hcases : u = w ∨ u = cyc.toHom 0 := by
    simpa only [outsiderEdge, Sym2.mem_iff] using he
  rcases hcases with h | h
  · exact huw h
  · exact hu ⟨0, h.symm⟩

/-- The w-v0 host spoke can repeat a selected consecutive edge color only at
source step zero. This uses the checked arbitrary-choice NEW endpoint lemma. -/
theorem gamma_ne_sourceStep_of_pos {m : ℕ}
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (w : Fin n) (hw : w ∉ Set.range cyc.toHom) (j : Fin m) (hj : 1 ≤ j.val) :
    χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceStep j)) := by
  have hv0 : cyc.toHom 0 ∉ (cyc.mapEdgeSet (sourceStep j)).val := by
    intro hv
    change cyc.toHom 0 ∈ Sym2.map cyc.toHom (sourceStep j).val at hv
    obtain ⟨k, hk, hk0⟩ := Sym2.mem_map.mp hv
    have hkey : k = (0 : Fin (m + 1)) := cyc.injective hk0
    subst k
    change (0 : Fin (m + 1)) ∈ s(Fin.castSucc j, Fin.succ j) at hk
    rcases Sym2.mem_iff.mp hk with h | h
    · have hval : (0 : ℕ) = j.val := by
        simpa only [Fin.val_zero, Fin.val_castSucc] using congrArg Fin.val h
      omega
    · have hval : (0 : ℕ) = j.val + 1 := by
        simpa only [Fin.val_zero, Fin.val_succ] using congrArg Fin.val h
      omega
  have hdisj : ∀ v : Fin n, v ∈ (cyc.mapEdgeSet (sourceStep j)).val →
      v ∉ (outsiderEdge cyc w hw 0).val := by
    intro v hve hvgamma
    have hcases : v = w ∨ v = cyc.toHom 0 := by
      simpa only [outsiderEdge, Sym2.mem_iff] using hvgamma
    rcases hcases with h | h
    · subst v
      exact outside_not_selected_cycle_edge χ r cyc w hw (sourceStep j) hve
    · subst v
      exact hv0 hve
  intro heq
  exact (arbitrary_selected_edge_ne_disjoint_host_edge χ r
    (cyc.mapEdgeSet (sourceStep j)) (outsiderEdge cyc w hw 0) hdisj) heq.symm

/-- Positive left J insertion. The extra gamma guard is discharged by a
contradiction in Case B under no rainbow C_(m+2). The bridge is the literal
selected uw edge, whose color is NEW at u and differs from alpha. -/
theorem positive_jLeft_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C) (hαnew : α ∈ newColors χ u)
    (_hselected : (selectedGraph χ r).Adj u w)
    (hδnew : χ (betweenEdge u w huw) ∈ newColors χ u)
    (hδα : χ (betweenEdge u w huw) ≠ α)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (hgamma : χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceStep (⟨0, by omega⟩ : Fin m)))) :
    IsRainbow (jLeftCopy hm cyc u w hu hw huw).toHom χ := by
  have hαγ : α ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u α hαnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  have hδγ : χ (betweenEdge u w huw) ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u _ hδnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  apply three_inserted_palette_isRainbow χ r cyc
    (jLeftCopy hm cyc u w hu hw huw) RetainedLeft
    (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
    α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0))
    hδα.symm hαγ hδγ
  · intro d hd
    refine ⟨outside_new_ne_selected_cycle_color χ r cyc u hu α hαnew d,
      outside_new_ne_selected_cycle_color χ r cyc u hu _ hδnew d, ?_⟩
    obtain ⟨j, _, hjEq⟩ := hd
    subst d
    by_cases hj0 : j.val = 0
    · have hidx : j = (⟨0, by omega⟩ : Fin m) := Fin.ext hj0
      simpa only [hidx] using hgamma
    · exact gamma_ne_sourceStep_of_pos χ r cyc w hw j (by omega)
  · intro e
    exact jLeft_edge_classes hm χ r cyc u w hu hw huw α hcommon e

/-- Positive right J insertion. It retains only consecutive selected source
steps with index at least two and the original selected closing edge. -/
theorem positive_jRight_insertion_copy {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r)) (u w : Fin n)
    (hu : u ∉ Set.range cyc.toHom) (hw : w ∉ Set.range cyc.toHom)
    (huw : u ≠ w) (α : C) (hαnew : α ∈ newColors χ u)
    (_hselected : (selectedGraph χ r).Adj u w)
    (hδnew : χ (betweenEdge u w huw) ∈ newColors χ u)
    (hδα : χ (betweenEdge u w huw) ≠ α)
    (hcommon : ∀ i : Fin (m + 1), χ (outsiderEdge cyc u hu i) = α)
    (hgamma : χ (outsiderEdge cyc w hw 0) ≠
      restrictedColor χ r (cyc.mapEdgeSet (sourceClosing m hm))) :
    IsRainbow (jRightCopy hm cyc u w hu hw huw).toHom χ := by
  have hαγ : α ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u α hαnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  have hδγ : χ (betweenEdge u w huw) ≠ χ (outsiderEdge cyc w hw 0) :=
    new_color_ne_edge_of_not_mem χ u _ hδnew _
      (outside_not_gamma_edge χ r cyc u w hu hw huw)
  apply three_inserted_palette_isRainbow χ r cyc
    (jRightCopy hm cyc u w hu hw huw) (RetainedRight hm)
    (sourceStep (⟨2, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨1, by omega⟩ : Fin (m + 1)))
    (sourceStep (⟨0, by omega⟩ : Fin (m + 1)))
    α (χ (betweenEdge u w huw)) (χ (outsiderEdge cyc w hw 0))
    hδα.symm hαγ hδγ
  · intro d hd
    refine ⟨outside_new_ne_selected_cycle_color χ r cyc u hu α hαnew d,
      outside_new_ne_selected_cycle_color χ r cyc u hu _ hδnew d, ?_⟩
    rcases hd with ⟨j, hj, hjEq⟩ | hjClosing
    · subst d
      exact gamma_ne_sourceStep_of_pos χ r cyc w hw j (by omega)
    · subst d
      exact hgamma
  · intro e
    exact jRight_edge_classes hm χ r cyc u w hu hw huw α hcommon e

end ErdosProblems.AntiRamseyCycleClaimOneJInsertion
