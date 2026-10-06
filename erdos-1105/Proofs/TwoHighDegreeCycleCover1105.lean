module

public import CycleContactCap1105
public import ActualCycleOutside1105
public import CycleCopy1105
public import TwoOutsiderCycleCover1105
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
The contact toggle needs a lower degree bound only at the
queried outsider. Two actual high-degree outsiders of an actual original
2d-cycle then give an original d-vertex cover. Other vertices may have low
degree. The actual cycle and these two outsiders are explicit auxiliary
inputs; their internal acquisition and universal connectedness assembly remain
separate obligations. No supplied common half, contacts, cover or global
minimum-degree assumption is introduced.
-/

noncomputable section

namespace ErdosProblems.PathUpperReduction.TwoHighDegreeCycleCover1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CycleContactCap1105
open ErdosProblems.PathUpperReduction.CycleCopy1105
open ErdosProblems.PathUpperReduction.TwoOutsiderCycleCover1105

/-- Only the actual queried outsider needs the original degree bound. -/
theorem actual_contact_card_and_successor_toggle_of_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) (hdegreez : d ≤ G.degree z) :
    (actualContacts G c z).card = d ∧
      ∀ i : Fin (n + 3), G.Adj z (c (i + 1)) ↔ ¬G.Adj z (c i) := by
  let N := actualContacts G c z
  have hdegree : N.card = G.degree z :=
    contact_card_eq_degree_of_outside_independence G c hind z hz
  have hN : d ≤ N.card := by rw [hdegree]; exact hdegreez
  have havoid : ∀ i ∈ N, finRotate (n + 3) i ∉ N := by
    intro i hi hnext
    have hzi : G.Adj z (c i) := (Finset.mem_filter.mp hi).2
    have hznext : G.Adj z (c (finRotate (n + 3) i)) :=
      (Finset.mem_filter.mp hnext).2
    rw [finRotate_apply] at hznext
    have hedge : (cycleGraph (n + 3)).Adj i (i + 1) := by
      simp [cycleGraph_adj]
    exact no_fresh_cycle_edge_contacts G d hconn hcard hfree c hsize
      i (i + 1) hedge z hz ⟨hzi, hznext⟩
  obtain ⟨_, _, hNcard, _, htoggle⟩ :=
    CycleHalfAlternation1105.half_partition_and_alternation
      (finRotate (n + 3)) N d (by simpa only [Fintype.card_fin] using hsize) hN havoid
  refine ⟨hNcard, ?_⟩
  intro i
  simpa only [finRotate_apply, N, actualContacts, Finset.mem_filter,
    Finset.mem_univ, true_and] using htoggle i

local instance {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-- An actual original cycle and two actual high-degree seed outsiders suffice.
The outside independence and both alternating contact sets are derived here. -/
theorem exists_actual_cover_of_cycle_and_two_high_degree_outsiders
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlength : C.length = 2 * d)
    (u v : V) (hu : u ∉ C.support) (hv : v ∉ C.support) (hne : u ≠ v)
    (hdegreeu : d ≤ G.degree u) (hdegreev : d ≤ G.degree v) :
    ∃ A : Finset V, A.card = d ∧ G.IsVertexCover (A : Set V) := by
  classical
  have hthree : 3 ≤ 2 * d := by
    rw [← hlength]
    exact hC.three_le_length
  let n : ℕ := 2 * d - 3
  have hsize : n + 3 = 2 * d := by dsimp only [n]; omega
  obtain ⟨c0, _henum, hrange0⟩ := exists_cycle_copy_with_exact_support G C hC
  obtain ⟨c, hrange⟩ :
      ∃ c : (cycleGraph (n + 3)).Copy G,
        Set.range c = {w | w ∈ C.support} := by
    rw [hsize, ← hlength]
    exact ⟨c0, hrange0⟩
  have hu' : u ∉ Set.range c := by
    rw [hrange]
    exact hu
  have hv' : v ∉ Set.range c := by
    rw [hrange]
    exact hv
  have hindC := ActualCycleOutside1105.outside_independent_of_actual_cycle
    G hconn d hfree C hC hlength
  have houtside : ∀ x y : V,
      x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y := by
    intro x y hx hy
    have hx' : x ∉ C.support := by
      intro hxC
      apply hx
      rw [hrange]
      exact hxC
    have hy' : y ∉ C.support := by
      intro hyC
      apply hy
      rw [hrange]
      exact hyC
    exact hindC x y hx' hy'
  have htoggleu := actual_contact_card_and_successor_toggle_of_degree
    G d hconn hcard hfree c hsize houtside u hu' hdegreeu
  have htogglev := actual_contact_card_and_successor_toggle_of_degree
    G d hconn hcard hfree c hsize houtside v hv' hdegreev
  have hfree' : (pathGraph (n + 5)).Free G := by
    have horder : n + 5 = 2 * d + 2 := by omega
    rw [horder]
    exact hfree
  exact exists_actual_cover_of_two_outsider_toggles G c hsize hfree'
    u v hu' hv' hne htoggleu.2 htogglev.2 houtside

end ErdosProblems.PathUpperReduction.TwoHighDegreeCycleCover1105
