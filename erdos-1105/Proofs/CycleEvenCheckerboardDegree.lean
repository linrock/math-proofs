module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.Nat.Even
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
graph degree obstruction for the exceptional even checkerboard
in the conditional #1105 cross-component argument. No host coloring,
selected component transport, Hamiltonian order or chord rotation is proved.
-/

namespace ErdosProblems.AntiRamseyEvenCheckerboardDegree

open scoped Classical

/-- In an even finite index set, if every graph edge has opposite endpoint
parities, quotient by two injects each neighbor set into `Fin (a / 2)`.
The statement uses arbitrary `G`; its adjacency is decided classically. -/
theorem degree_le_half_of_no_same_parity_edge
    {a : ℕ} (ha : Even a) (G : SimpleGraph (Fin a))
    (hno : ∀ x y : Fin a, G.Adj x y → x.val % 2 ≠ y.val % 2)
    (x : Fin a) : G.degree x ≤ a / 2 := by
  let f : G.neighborSet x → Fin (a / 2) := fun j =>
    ⟨j.val.val / 2, by
      have hjlt : j.val.val < a := j.val.isLt
      have haMod : a % 2 = 0 := Nat.even_iff.mp ha
      omega⟩
  have hinj : Function.Injective f := by
    intro j l h
    have hquot : j.val.val / 2 = l.val.val / 2 := congrArg Fin.val h
    have hjParity : x.val % 2 ≠ j.val.val % 2 := hno x j.val j.property
    have hlParity : x.val % 2 ≠ l.val.val % 2 := hno x l.val l.property
    have hval : j.val.val = l.val.val := by omega
    exact Subtype.ext (Fin.ext hval)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [SimpleGraph.card_neighborSet_eq_degree, Fintype.card_fin] using hcard

/-- The exact cross-pair degree lower bound rules out opposite-parity-only
edges in both even graphs whose orders are at most `k - 1`, for even `k`.
The output is an actual adjacent same-parity pair in one supplied graph. -/
theorem exists_same_parity_edge_of_cross_degree_sum
    {k a b : ℕ} (hk : 5 ≤ k) (hkEven : Even k)
    (ha : 3 ≤ a) (haEven : Even a) (haUpper : a ≤ k - 1)
    (hb : 3 ≤ b) (hbEven : Even b) (hbUpper : b ≤ k - 1)
    (GA : SimpleGraph (Fin a)) (GB : SimpleGraph (Fin b))
    (hpair : ∀ x : Fin a, ∀ y : Fin b,
      k - 1 ≤ GA.degree x + GB.degree y) :
    (∃ x y : Fin a, GA.Adj x y ∧ x.val % 2 = y.val % 2) ∨
      (∃ x y : Fin b, GB.Adj x y ∧ x.val % 2 = y.val % 2) := by
  by_contra hnone
  have hnoA : ∀ x y : Fin a, GA.Adj x y → x.val % 2 ≠ y.val % 2 := by
    intro x y hxy hpar
    exact hnone (Or.inl ⟨x, y, hxy, hpar⟩)
  have hnoB : ∀ x y : Fin b, GB.Adj x y → x.val % 2 ≠ y.val % 2 := by
    intro x y hxy hpar
    exact hnone (Or.inr ⟨x, y, hxy, hpar⟩)
  let x0 : Fin a := ⟨0, by omega⟩
  let y0 : Fin b := ⟨0, by omega⟩
  have hdegreeA : GA.degree x0 ≤ a / 2 :=
    degree_le_half_of_no_same_parity_edge haEven GA hnoA x0
  have hdegreeB : GB.degree y0 ≤ b / 2 :=
    degree_le_half_of_no_same_parity_edge hbEven GB hnoB y0
  have hkMod : k % 2 = 0 := Nat.even_iff.mp hkEven
  have haMod : a % 2 = 0 := Nat.even_iff.mp haEven
  have hbMod : b % 2 = 0 := Nat.even_iff.mp hbEven
  have haStrict : a ≤ k - 2 := by omega
  have hbStrict : b ≤ k - 2 := by omega
  have hsumUpper : GA.degree x0 + GB.degree y0 ≤ k - 2 := by omega
  have hsumLower := hpair x0 y0
  omega

end ErdosProblems.AntiRamseyEvenCheckerboardDegree
