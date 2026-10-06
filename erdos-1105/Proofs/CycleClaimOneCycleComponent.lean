module

public import CycleClaimOneSelectedAttachmentV2
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
selected component implication of Claim 1. This proves no component existence, weak partition,
numerical upper bound, or universal #1105 declaration at this source stage.
-/

namespace ErdosProblems.AntiRamseyCycleClaimOneCycleComponent

open Finset SimpleGraph
open ErdosProblems.AntiRamseyCycleNewColors
open ErdosProblems.AntiRamseyCycleNewChoiceExchange
open ErdosProblems.AntiRamseyCycleClaimOneSelectedAttachment

variable {n : ℕ} {C : Type*} [DecidableEq C]

/-- A selected component containing one vertex of an old selected cycle has
exactly that cycle image, under the original high-NEW and host no-rainbow
conditions. Preconnectedness supplies every other cycle vertex in D. -/
theorem selected_component_support_eq_cycle_range {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent)
    (hzeroD : cyc.toHom 0 ∈ D.supp) : D.supp = Set.range cyc.toHom := by
  classical
  let G : SimpleGraph (Fin n) := selectedGraph χ r
  have hclosed : ∀ a b : Fin n, a ∈ Set.range cyc.toHom → G.Adj a b →
      b ∈ Set.range cyc.toHom := by
    rintro a b ⟨i, rfl⟩ hab
    by_contra hb
    exact no_rainbow_no_outside_selected_attachment hm χ r cyc b hb
      (hnew b) hnone i hab.symm
  have hgen : ∀ z : Fin n,
      Relation.ReflTransGen G.Adj (cyc.toHom 0) z → z ∈ Set.range cyc.toHom := by
    intro z hz
    induction hz with
    | refl => exact ⟨0, rfl⟩
    | tail _ hab ih => exact hclosed _ _ ih hab
  have hsubset : D.supp ⊆ Set.range cyc.toHom := by
    intro z hzD
    exact hgen z ((G.reachable_iff_reflTransGen _ _).mp
      (D.reachable_of_mem_supp hzeroD hzD))
  have hsupset : Set.range cyc.toHom ⊆ D.supp := by
    rintro z ⟨i, rfl⟩
    have hreach : G.Reachable (cyc.toHom 0) (cyc.toHom i) :=
      Reachable.map cyc.toHom (cycleGraph_preconnected (n := m + 1) 0 i)
    have hcomp : G.connectedComponentMk (cyc.toHom 0) =
        G.connectedComponentMk (cyc.toHom i) := ConnectedComponent.sound hreach
    exact (D.mem_supp_iff _).mpr
      (hcomp.symm.trans ((D.mem_supp_iff _).mp hzeroD))
  exact Set.Subset.antisymm hsubset hsupset

/-- The exact selected component order is the old cycle order. -/
theorem selected_component_card_eq_cycle_order {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r))
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent)
    (hzeroD : cyc.toHom 0 ∈ D.supp) : D.supp.ncard = m + 1 := by
  rw [selected_component_support_eq_cycle_range hm χ r cyc hnew hnone D hzeroD]
  simpa only [Nat.card_fin] using Set.ncard_range_of_injective cyc.injective

/-- Exact component-local old-cycle exclusion for the oversized branch.
The same component support appears in its size and cycle-containment inputs. -/
theorem oversized_component_excludes_selected_cycle {m : ℕ} (hm : 2 ≤ m)
    (χ : TopEdgeLabeling (Fin n) C) (r : NewChoice χ)
    (hnew : ∀ v : Fin n, 2 ≤ (newColors χ v).card)
    (hnone : ∀ f : (cycleGraph (m + 2)).Copy (⊤ : SimpleGraph (Fin n)),
      ¬ IsRainbow f.toHom χ)
    (D : (selectedGraph χ r).ConnectedComponent) (hlarge : m + 1 < D.supp.ncard) :
    ∀ cyc : (cycleGraph (m + 1)).Copy (selectedGraph χ r),
      ¬ (∀ i : Fin (m + 1), cyc.toHom i ∈ D.supp) := by
  intro cyc hinside
  have hcard := selected_component_card_eq_cycle_order hm χ r cyc hnew hnone D
    (hinside 0)
  omega

end ErdosProblems.AntiRamseyCycleClaimOneCycleComponent
