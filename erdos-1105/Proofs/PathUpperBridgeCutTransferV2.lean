module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
for the graph-only cut transfer used by the finite
common-bridge exchange descent. The original bridge is an actual edge of R,
is retained as an actual edge of connected D, and all other D edges respect
the original single-edge deletion components. No current bridge or reverse
deletion reachability is assumed. The carrier need not be finite.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

universe w

/-- The current graph's deletion has exactly the original bridge cut's
reachability relation when every other current edge respects that cut. -/
theorem bridge_cut_component_transfer
    {V : Type w} (R D : SimpleGraph V) {u v : V}
    (_hR : R.Connected) (_hRb : R.Adj u v)
    (hbR : R.IsBridge s(u, v))
    (hD : D.Connected) (_hDb : D.Adj u v)
    (hrespect : ∀ {a b : V}, D.Adj a b →
      s(a, b) ≠ s(u, v) →
      (R.deleteEdges {s(u, v)}).Reachable a b) :
    ∀ a b : V,
      (D.deleteEdges {s(u, v)}).Reachable a b ↔
      (R.deleteEdges {s(u, v)}).Reachable a b := by
  classical
  let R₀ := R.deleteEdges {s(u, v)}
  let D₀ := D.deleteEdges {s(u, v)}
  have hnotRuv : ¬ R₀.Reachable u v := SimpleGraph.isBridge_iff.mp hbR
  have hforward : ∀ {a b : V}, D₀.Reachable a b → R₀.Reachable a b := by
    intro a b hab
    obtain ⟨p⟩ := hab
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b _c hab _p ih =>
      have hadj : D.Adj a b := (SimpleGraph.deleteEdges_adj.mp hab).1
      have hne : s(a, b) ≠ s(u, v) := by
        simpa using (SimpleGraph.deleteEdges_adj.mp hab).2
      exact (hrespect hadj hne).trans ih
  have hcoverWalk : ∀ {a b : V}, (p : D.Walk a b) →
      (D₀.Reachable u b ∨ D₀.Reachable v b) →
      (D₀.Reachable u a ∨ D₀.Reachable v a) := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b _c hab _p ih =>
      intro h
      by_cases he : s(a, b) = s(u, v)
      · rcases Sym2.eq_iff.mp he with ⟨ha, _⟩ | ⟨ha, _⟩
        · left
          rw [ha]
        · right
          rw [ha]
      · have hstep : D₀.Adj a b :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using he⟩
        rcases ih h with hu | hv
        · exact Or.inl (hu.trans hstep.symm.reachable)
        · exact Or.inr (hv.trans hstep.symm.reachable)
  have hcover : ∀ a : V, D₀.Reachable u a ∨ D₀.Reachable v a := by
    intro a
    obtain ⟨p⟩ := hD.preconnected a u
    exact hcoverWalk p (Or.inl (SimpleGraph.Reachable.refl u))
  intro a b
  constructor
  · exact hforward
  · intro hab
    rcases hcover a with hau | hva
    · rcases hcover b with hub | hvb
      · exact hau.symm.trans hub
      · exfalso
        exact hnotRuv ((hforward hau).trans (hab.trans (hforward hvb).symm))
    · rcases hcover b with hub | hvb
      · exfalso
        exact hnotRuv ((hforward hub).trans (hab.symm.trans (hforward hva).symm))
      · exact hva.symm.trans hvb

end ErdosProblems.PathUpperReduction
