module

public import CycleSelectedComponentHamiltonianV4
public import CycleComponentHamiltonianNonbridgeV3
public import CycleCrossComponentPaletteExclusionV2

@[expose] public section

/-!
original-hypothesis caller for the cross-component NEW-palette
exclusion.
-/

namespace ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion

open SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewRepresentative
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleSelectedComponentOrder
open ErdosProblems.AntiRamseyCycleSelectedComponentHamiltonian
open ErdosProblems.AntiRamseyCycleComponentHamiltonianNonbridge
open ErdosProblems.AntiRamseyCycleCrossComponentPaletteExclusion

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- Under the original high-NEW and distinct-pair bounds, every original host
edge between distinct whole selected components has color outside the full
NEW union. The valid choice and the original color type are arbitrary. -/
theorem cross_edge_color_not_new_union {k : ℕ} (hk : 5 ≤ k)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hpair : ∀ u v : Fin n, u ≠ v →
      k - 1 ≤ (newColors χ u).card + (newColors χ v).card)
    (hno : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (A B : (selectedGraph χ r).ConnectedComponent) (hAB : A ≠ B)
    (u v : Fin n) (hu : u ∈ A.supp) (hv : v ∈ B.supp)
    (e : HostEdge n) (he : e.val = s(u, v)) :
    χ e ∉ newColorUnion χ := by
  classical
  have hupper : ∀ r' : NewChoice χ,
      ∀ D : (selectedGraph χ r').ConnectedComponent, D.supp.ncard ≤ k - 1 := by
    intro r' D
    exact selected_component_order_le_original hk χ r' hnew hpair hno D
  have hcycles : ∀ D : (selectedGraph χ r).ConnectedComponent,
      ∃ (x : D) (c : D.toSimpleGraph.Walk x x), c.IsHamiltonianCycle := by
    intro D
    obtain ⟨_, _, _, _, hcycle⟩ :=
      selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno D
    exact hcycle
  have hnb : ∀ c : newColorUnion χ,
      ¬ (selectedGraph χ r).IsBridge (r.edge c).val := by
    intro c
    apply not_isBridge_of_component_hamiltonian_cycles (selectedGraph χ r) hcycles
    rw [selectedGraph_edgeSet χ r]
    exact ⟨c, rfl⟩
  have hAlower : k + 1 ≤ 2 * A.supp.ncard :=
    (selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno A).2.1
  have hBlower : k + 1 ≤ 2 * B.supp.ncard :=
    (selected_component_size_bounds_and_hamiltonian_cycle hk χ r hnew hpair hno B).2.1
  have hlarge : k + 1 ≤ A.supp.ncard + B.supp.ncard := by omega
  have hdisjoint : Disjoint A.supp B.supp :=
    (selectedGraph χ r).pairwise_disjoint_supp_connectedComponent hAB
  exact cross_edge_color_not_new_union_of_nonbridge χ r hnb hupper A B
    hdisjoint hlarge u v hu hv e he

end ErdosProblems.AntiRamseyCycleOriginalCrossComponentPaletteExclusion
