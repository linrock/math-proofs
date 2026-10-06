module

public import DiamondColorChoice

@[expose] public section

/-!
A rooted diamond supplies a Hamiltonian path avoiding one extra color. Two
distinct pendant colors supply a second edge avoiding that color. These are
only finite color-choice facts; the Formal Conjectures copy is built in the
next module.
-/

namespace ErdosProblems.AntiRamseyPathSixTransfer

open ErdosProblems.AntiRamseyPathFiveUpper

variable {C : Type*}

/-- The first five of seven distinct selected colors belong to the rooted
diamond; the final two are the pendant edges. -/
def pathSixCoreColors (d : Fin 7 → C) : Fin 5 → C :=
  fun i => d ⟨i.val, by omega⟩

/-- Remove the pendant-edge position from a five-edge path. The two inputs
`0` and `1` deliberately share output `0`; injectivity is used only away
from input `1`. -/
def pathSixCompress (i : Fin 5) : Fin 4 :=
  if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 1
  else if i = 3 then 2 else 3

/-- `true` uses the first pendant color, and `false` the second. -/
def pathSixPendantIndex (s : Bool) : Fin 7 := if s then 5 else 6

/-- Five consecutive edge colors: outside-to-outside, pendant, then three
edges of a rooted diamond Hamiltonian path. -/
def pathSixChosenColors (d : Fin 7 → C) (z : C)
    (s : Bool) (r : Fin 4) (i : Fin 5) : C :=
  if i = 1 then d (pathSixPendantIndex s)
  else extendedPathColors (pathSixCoreColors d) z r (pathSixCompress i)

theorem pathSixCompress_injective_away_pendant :
    ∀ i j : Fin 5, i ≠ 1 → j ≠ 1 →
      pathSixCompress i = pathSixCompress j → i = j := by
  decide

theorem pathSixPendantIndex_ge_five (s : Bool) :
    5 ≤ (pathSixPendantIndex s).val := by
  cases s <;> decide

theorem pendant_color_ne_core (d : Fin 7 → C)
    (hd : Function.Injective d) (s : Bool) (j : Fin 5) :
    d (pathSixPendantIndex s) ≠ pathSixCoreColors d j := by
  intro he
  have hindex := congrArg Fin.val (hd he)
  have hbig := pathSixPendantIndex_ge_five s
  dsimp [pathSixCoreColors] at hindex
  omega

theorem pendant_color_ne_extended (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) (s : Bool) (r : Fin 4)
    (hz : d (pathSixPendantIndex s) ≠ z) (j : Fin 4) :
    d (pathSixPendantIndex s) ≠
      extendedPathColors (pathSixCoreColors d) z r j := by
  by_cases hj : j = 0
  · simpa [extendedPathColors, hj] using hz
  · simpa [extendedPathColors, hj] using
      pendant_color_ne_core d hd s (diamondPathEdgeIndex r j)

theorem pathSixChosenColors_injective (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) (s : Bool) (r : Fin 4)
    (hr : Function.Injective
      (extendedPathColors (pathSixCoreColors d) z r))
    (hz : d (pathSixPendantIndex s) ≠ z) :
    Function.Injective (pathSixChosenColors d z s r) := by
  intro i j hij
  by_cases hi : i = 1
  · subst i
    by_cases hj : j = 1
    · subst j
      rfl
    · have he : d (pathSixPendantIndex s) =
          extendedPathColors (pathSixCoreColors d) z r
            (pathSixCompress j) := by
        simpa [pathSixChosenColors, hj] using hij
      exact False.elim
        ((pendant_color_ne_extended d hd z s r hz (pathSixCompress j)) he)
  · by_cases hj : j = 1
    · subst j
      have he : extendedPathColors (pathSixCoreColors d) z r
          (pathSixCompress i) = d (pathSixPendantIndex s) := by
        simpa [pathSixChosenColors, hi] using hij
      exact False.elim
        ((pendant_color_ne_extended d hd z s r hz (pathSixCompress i)) he.symm)
    · have he : extendedPathColors (pathSixCoreColors d) z r
          (pathSixCompress i) =
          extendedPathColors (pathSixCoreColors d) z r
            (pathSixCompress j) := by
        simpa [pathSixChosenColors, hi, hj] using hij
      exact pathSixCompress_injective_away_pendant i j hi hj (hr he)

/-- Among the two pendant choices and four rooted-diamond Hamiltonian paths,
one produces five distinct colors for every outside-to-outside host color. -/
theorem pathSix_color_choice (d : Fin 7 → C)
    (hd : Function.Injective d) (z : C) :
    ∃ (s : Bool) (r : Fin 4),
      Function.Injective (pathSixChosenColors d z s r) := by
  have hcore : Function.Injective (pathSixCoreColors d) := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin 7 => x.val) (hd hij))
  obtain ⟨r, hr⟩ :=
    diamond_color_choice (pathSixCoreColors d) hcore z
  by_cases h : z = d 5
  · refine ⟨false, r, ?_⟩
    have hz : d (pathSixPendantIndex false) ≠ z := by
      rw [h]
      simpa [pathSixPendantIndex] using
        (hd.ne (by decide : (6 : Fin 7) ≠ 5))
    exact pathSixChosenColors_injective d hd z false r hr hz
  · refine ⟨true, r, ?_⟩
    have hz : d (pathSixPendantIndex true) ≠ z := by
      simpa [pathSixPendantIndex] using (Ne.symm h)
    exact pathSixChosenColors_injective d hd z true r hr hz

end ErdosProblems.AntiRamseyPathSixTransfer
