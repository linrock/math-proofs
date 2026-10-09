module

public import Solution
public import Statement

@[expose] public section

/-! Full statement, imported-definition unfolding, fidelity, and
transitive-axiom checks for the submitted Erdős #1105 endpoints. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. -/

open SimpleGraph Asymptotics Filter

namespace Erdos1105.Palomar

/-- The separately stated Part (i) target is definitionally the proved proposition. -/
theorem statement_i_fidelity : Erdos1105.Challenge.statement_i :=
  Erdos1105.erdos_1105.parts.i

/-- The separately stated Part (ii) target is definitionally the proved proposition. -/
theorem statement_ii_fidelity : Erdos1105.Challenge.statement_ii :=
  Erdos1105.erdos_1105.parts.ii

/-- `Erdos1105.Palomar.IsRainbow` is definitionally identical to `SimpleGraph.IsRainbow`. -/
theorem isRainbow_def_eq : @Erdos1105.Palomar.IsRainbow = @SimpleGraph.IsRainbow :=
  rfl

/-- `Erdos1105.Palomar.antiRamseyNum` is definitionally identical to `SimpleGraph.antiRamseyNum`. -/
theorem antiRamseyNum_def_eq : @Erdos1105.Palomar.antiRamseyNum = @SimpleGraph.antiRamseyNum :=
  rfl

/-- `SimpleGraph.EdgeLabeling G K` is definitionally `G.edgeSet → K`. -/
theorem edgeLabeling_def_eq {V : Type*} (G : SimpleGraph V) (K : Type*) :
    G.EdgeLabeling K = (G.edgeSet → K) :=
  rfl

/-- `SimpleGraph.TopEdgeLabeling V K` is definitionally `(⊤ : SimpleGraph V).edgeSet → K`. -/
theorem topEdgeLabeling_def_eq (V K : Type*) :
    TopEdgeLabeling V K = ((⊤ : SimpleGraph V).edgeSet → K) :=
  rfl

/-- `SimpleGraph.EdgeLabeling.pullback c f` is definitionally `c ∘ f.mapEdgeSet`. -/
theorem pullback_def_eq {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (c : G.EdgeLabeling K) (f : H →g G) :
    c.pullback f = (c ∘ f.mapEdgeSet) :=
  rfl

/-- `IsRainbow f c` is definitionally `Function.Injective (c ∘ f.mapEdgeSet)`. -/
theorem isRainbow_unfolded {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H →g G) (c : G.EdgeLabeling K) :
    IsRainbow f c ↔ Function.Injective (c ∘ f.mapEdgeSet) :=
  Iff.rfl

/-- `antiRamseyNum H n` unfolds definitionally to the supremum of `k` over surjective
edge-colorings `c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin k` with no copy `f : H.Copy ⊤`
whose induced edge-set labeling `c ∘ f.toHom.mapEdgeSet` is injective. -/
theorem antiRamseyNum_unfolded {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) :
    antiRamseyNum H n =
      sSup {k : ℕ | ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin k,
        Function.Surjective c ∧
        ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)),
          ¬Function.Injective (c ∘ f.toHom.mapEdgeSet)} :=
  rfl

/-- Every `f : H.Copy G` is an injective vertex map preserving adjacency. -/
theorem copy_iff_injective_hom {α V : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H.Copy G) :
    Function.Injective f.toHom ∧ ∀ ⦃u v : α⦄, H.Adj u v → G.Adj (f.toHom u) (f.toHom v) :=
  ⟨f.injective, fun _ _ h => f.toHom.map_adj h⟩

/-- `cycleGraph (n + 2)` has adjacency `u - v = 1 ∨ v - u = 1` in `Fin (n + 2)`. -/
theorem cycleGraph_adj_audit (n : ℕ) (u v : Fin (n + 2)) :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 :=
  Iff.rfl

/-- `pathGraph n` has adjacency `u.val + 1 = v.val ∨ v.val + 1 = u.val` in `Fin n`. -/
theorem pathGraph_adj_audit (n : ℕ) (u v : Fin n) :
    (pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
  SimpleGraph.pathGraph_adj

/-- `f =O[l] g` is `∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`. -/
theorem isBigO_iff_audit {α : Type*} (l : Filter α) (f g : α → ℝ) :
    (f =O[l] g) ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  Asymptotics.isBigO_iff

end Erdos1105.Palomar

#print SimpleGraph.EdgeLabeling
#print SimpleGraph.TopEdgeLabeling
#print SimpleGraph.EdgeLabeling.pullback
#print SimpleGraph.Hom
#print SimpleGraph.Hom.mapEdgeSet
#print SimpleGraph.Copy
#print SimpleGraph.Copy.toHom
#print SimpleGraph.Copy.injective
#print SimpleGraph.cycleGraph
#print SimpleGraph.hasse
#print SimpleGraph.pathGraph
#print Asymptotics.IsBigOWith
#print Asymptotics.IsBigO
#print Filter.atTop
#print SimpleGraph.IsRainbow
#print SimpleGraph.antiRamseyNum
#print Erdos1105.Palomar.IsRainbow
#print Erdos1105.Palomar.antiRamseyNum
#print Erdos1105.Challenge.statement_i
#print Erdos1105.Challenge.statement_ii
#print Erdos1105.Palomar.erdos_1105_cycles
#print Erdos1105.Palomar.erdos_1105_paths
#print Erdos1105.Palomar.erdos_1105_parts_i
#print Erdos1105.Palomar.erdos_1105_parts_ii
#print Erdos1105.Palomar.antiRamseyNum_triangle
#print Erdos1105.Palomar.cycle_fullBlock_lower
#print Erdos1105.Palomar.cycle_real_lower
#print Erdos1105.Palomar.cycle_linear_upper
#print Erdos1105.erdos_1105.parts.i
#print Erdos1105.erdos_1105.parts.ii
#print axioms Erdos1105.Palomar.erdos_1105_cycles
#print axioms Erdos1105.Palomar.erdos_1105_paths
#print axioms Erdos1105.Palomar.erdos_1105_parts_i
#print axioms Erdos1105.Palomar.erdos_1105_parts_ii
#print axioms Erdos1105.Palomar.antiRamseyNum_triangle
#print axioms Erdos1105.Palomar.cycle_fullBlock_lower
#print axioms Erdos1105.Palomar.cycle_real_lower
#print axioms Erdos1105.Palomar.cycle_linear_upper
#print axioms Erdos1105.erdos_1105.parts.i
#print axioms Erdos1105.erdos_1105.parts.ii
#print axioms Erdos1105.Palomar.statement_i_fidelity
#print axioms Erdos1105.Palomar.statement_ii_fidelity
