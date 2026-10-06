module

public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Group.Nat.Even
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Normalize an even-index same-parity chord by literal cyclic rotation

The graph is arbitrary and the original adjacent
pair is retained. Rotation is literally i ↦ x+i in Fin a and its chord offset
is literally y-x. NeZero a is constructed from a>=3 in the proof; no public
extra instance premise is imposed. No host color, NEW, selected component,
component degree, Hamiltonian window or Claim3 conclusion is proved here.
-/

namespace ErdosProblems.AntiRamseyEvenChordRotation

open SimpleGraph

def cyclicRotation {a : ℕ} (x : Fin a) : Fin a → Fin a := fun i => x + i

def chordOffset {a : ℕ} (x y : Fin a) : Fin a := y - x

/-- The literal cyclic rotation sends zero to x and the positive even chord
offset to y, preserves numeric cycleGraph adjacency, and pulls the original
edge back to an actual normalized chord. The explicit zero Fin record keeps
the statement free of an additional NeZero instance assumption. -/
theorem normalized_even_chord_rotation
    {a : ℕ} (ha : 3 ≤ a) (haEven : Even a)
    (G : SimpleGraph (Fin a)) (x y : Fin a)
    (hxy : G.Adj x y) (hparity : x.val % 2 = y.val % 2) :
    Function.Injective (cyclicRotation x) ∧
      cyclicRotation x (⟨0, by omega⟩ : Fin a) = x ∧
      cyclicRotation x (chordOffset x y) = y ∧
      Even (chordOffset x y).val ∧
      2 ≤ (chordOffset x y).val ∧
      (chordOffset x y).val + 2 ≤ a ∧
      (G.comap (cyclicRotation x)).Adj
        (⟨0, by omega⟩ : Fin a) (chordOffset x y) ∧
      (∀ i j : Fin a,
        (cycleGraph a).Adj (cyclicRotation x i) (cyclicRotation x j) ↔
          (cycleGraph a).Adj i j) := by
  let : NeZero a := ⟨by omega⟩
  have hinj : Function.Injective (cyclicRotation x) := add_right_injective x
  have hzero : cyclicRotation x (⟨0, by omega⟩ : Fin a) = x := by
    change x + (0 : Fin a) = x
    exact add_zero x
  have hendpoint : cyclicRotation x (chordOffset x y) = y := by
    change x + (y - x) = y
    exact add_sub_cancel x y
  have hdne : chordOffset x y ≠ (0 : Fin a) := by
    intro hd0
    change y - x = 0 at hd0
    exact hxy.ne (sub_eq_zero.mp hd0).symm
  have hdpos : 0 < (chordOffset x y).val := by
    by_contra hnot
    have hdval : (chordOffset x y).val = 0 := by omega
    have hd0 : chordOffset x y = (0 : Fin a) :=
      Fin.ext (by simpa only [Fin.val_zero] using hdval)
    exact hdne hd0
  have haMod : a % 2 = 0 := Nat.even_iff.mp haEven
  have hdMod : (chordOffset x y).val % 2 = 0 := by
    dsimp only [chordOffset]
    by_cases hle : x ≤ y
    · have hsub : (y - x).val = y.val - x.val := Fin.sub_val_of_le hle
      have hleval : x.val ≤ y.val := hle
      rw [hsub]
      omega
    · have hlt : y < x := lt_of_not_ge hle
      have hltval : y.val < x.val := hlt
      have hsub : (y - x).val = a + y.val - x.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      have hxlt : x.val < a := x.isLt
      rw [hsub]
      omega
  have hdlt : (chordOffset x y).val < a := (chordOffset x y).isLt
  have hdLower : 2 ≤ (chordOffset x y).val := by omega
  have hdUpper : (chordOffset x y).val + 2 ≤ a := by omega
  have hchord : (G.comap (cyclicRotation x)).Adj
      (⟨0, by omega⟩ : Fin a) (chordOffset x y) := by
    rw [SimpleGraph.comap_adj, hzero, hendpoint]
    exact hxy
  have hcycle (i j : Fin a) :
      (cycleGraph a).Adj (cyclicRotation x i) (cyclicRotation x j) ↔
        (cycleGraph a).Adj i j := by
    dsimp only [cyclicRotation]
    rw [cycleGraph_adj', cycleGraph_adj']
    simp only [add_sub_add_left_eq_sub]
  exact ⟨hinj, hzero, hendpoint, Nat.even_iff.mpr hdMod, hdLower, hdUpper,
    hchord, hcycle⟩

end ErdosProblems.AntiRamseyEvenChordRotation
