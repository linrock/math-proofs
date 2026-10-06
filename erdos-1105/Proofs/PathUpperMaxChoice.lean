module

public import PathUpperExchange

@[expose] public section

/-!
Finiteness of the edge-selection choices lets us choose a representative with
the largest possible connected component. This removes the extremal-choice
hypothesis from the cross-edge bridge confinement lemma.
-/

namespace ErdosProblems.PathUpperReduction

open SimpleGraph

variable {n q : ℕ}

/-- Surjectivity gives a selected host edge of every used color. -/
noncomputable def choiceOfSurjective (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) : RepresentativeChoice χ where
  edge := Function.surjInv hχ
  color_eq := Function.surjInv_eq hχ

set_option linter.style.haveILetI false in
/-- Among all same-color representatives, one has a globally largest
connected component. The condition `0<n` supplies a component vertex. -/
theorem exists_globallyLargestComponent (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n), GloballyLargestComponent χ r x := by
  classical
  letI : Fintype (HostEdge n) :=
    SimpleGraph.fintypeEdgeSet (⊤ : SimpleGraph (Fin n))
  have hinj : Function.Injective (fun r : RepresentativeChoice χ => r.edge) := by
    intro r s h
    cases r with
    | mk re rp =>
      cases s with
      | mk se sp =>
        cases h
        rfl
  letI : Finite (RepresentativeChoice χ) := Finite.of_injective _ hinj
  letI : Fintype (RepresentativeChoice χ × Fin n) := Fintype.ofFinite _
  let x₀ : Fin n := ⟨0, hn⟩
  let r₀ := choiceOfSurjective χ hχ
  obtain ⟨⟨r, x⟩, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (RepresentativeChoice χ × Fin n))
      (fun p => ((selectedGraph χ p.1).connectedComponentMk p.2).supp.ncard)
      ⟨(r₀, x₀), Finset.mem_univ _⟩
  exact ⟨r, x, fun r' z => hmax (r', z) (Finset.mem_univ _)⟩

/-- The first unconditional choice reduction in Yuan's upper proof: for any
surjective host coloring, choose one edge per color and a largest component;
every host edge leaving it has the color of a selected bridge *inside* it. -/
theorem exists_representative_with_cross_edge_bridge_colors
    (χ : TopEdgeLabeling (Fin n) (Fin q))
    (hχ : Function.Surjective χ) (hn : 0 < n) :
    ∃ (r : RepresentativeChoice χ) (x : Fin n),
      ∀ (e : HostEdge n) (u y : Fin n), e.val = s(u, y) →
        (selectedGraph χ r).Reachable x u →
        ¬ (selectedGraph χ r).Reachable x y →
        ∃ a b : Fin n,
          (r.edge (χ e)).val = s(a, b) ∧
          a ∈ (selectedGraph χ r).connectedComponentMk x ∧
          b ∈ (selectedGraph χ r).connectedComponentMk x ∧
          (selectedGraph χ r).IsBridge s(a, b) := by
  obtain ⟨r, x, hmax⟩ := exists_globallyLargestComponent χ hχ hn
  exact ⟨r, x, fun e u y he hu hy =>
    cross_edge_color_is_component_bridge χ r x hmax e u y he hu hy⟩

end ErdosProblems.PathUpperReduction
