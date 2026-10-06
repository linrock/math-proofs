module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

/-!
for the nonbridge premise in the arbitrary-choice
cross-component palette exclusion.
-/

namespace ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge

open SimpleGraph

/-- An injective pullback retains a bridge whose endpoints lie in its carrier. -/
theorem isBridge_comap_of_injective {V W : Type*}
    (G : SimpleGraph V) (f : W → V) (hf : Function.Injective f)
    {x y : W} (hbridge : G.IsBridge s(f x, f y)) :
    (G.comap f).IsBridge s(x, y) := by
  rw [SimpleGraph.isBridge_iff] at hbridge ⊢
  intro hreach
  let φ : (G.comap f).deleteEdges {s(x, y)} →g
      G.deleteEdges {s(f x, f y)} :=
    { toFun := f
      map_rel' := by
        intro u v huv
        obtain ⟨hadj, hnot⟩ := SimpleGraph.deleteEdges_adj.mp huv
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
        intro hmem
        have heq := Set.mem_singleton_iff.mp hmem
        have hpair : s(u, v) = s(x, y) := (Sym2.map.injective hf) heq
        exact hnot (Set.mem_singleton_iff.mpr hpair) }
  exact hbridge (hreach.map φ)

/-- If every whole component has a literal Hamiltonian cycle, no selected
edge is a bridge. No finite ambient carrier or connected ambient graph is assumed. -/
theorem not_isBridge_of_component_hamiltonian_cycles
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hcycles : ∀ D : G.ConnectedComponent,
      ∃ (u : D) (c : D.toSimpleGraph.Walk u u), c.IsHamiltonianCycle)
    {e : Sym2 V} (he : e ∈ G.edgeSet) : ¬ G.IsBridge e := by
  classical
  induction e with
  | h x y =>
    intro hbridge
    have hxy : G.Adj x y := he
    let D : G.ConnectedComponent := G.connectedComponentMk x
    let xD : D := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
    let yD : D := ⟨y, D.mem_supp_of_adj_mem_supp xD.property hxy⟩
    obtain ⟨u, c, hc⟩ := hcycles D
    let : Finite D := hc.finite
    let : Fintype D := Fintype.ofFinite D
    have hham : D.toSimpleGraph.IsHamiltonian := fun _ => ⟨u, c, hc⟩
    have hlocal : D.toSimpleGraph.IsBridge s(xD, yD) :=
      isBridge_comap_of_injective G (fun z : D => z.val)
        Subtype.val_injective hbridge
    exact hlocal.not_isHamiltonian hham

end ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge
