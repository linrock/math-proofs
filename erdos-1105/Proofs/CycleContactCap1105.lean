module

public import LongCycleOutside1105
public import CycleEdgeContact1105
public import CycleHalfAlternation1105
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Cycle contact bounds for vertices outside a `2d`-cycle in a `P_{2d+2}`-free
connected graph of order at least `2d + 2`, combining `LongCycleOutside1105`,
`CycleEdgeContact1105`, and `CycleHalfAlternation1105`.
-/

namespace ErdosProblems.PathUpperReduction.CycleContactCap1105

open SimpleGraph

/-- Original path freedom and host surplus forbid a fresh vertex's two
contacts to an actual edge of the supplied original cycle Copy. -/
theorem no_fresh_cycle_edge_contacts
    {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (u v : Fin (n + 3)) (huv : (cycleGraph (n + 3)).Adj u v)
    (z : V) (hz : z ∉ Set.range c) :
    ¬(G.Adj z (c u) ∧ G.Adj z (c v)) := by
  rintro ⟨hzu, hzv⟩
  obtain ⟨D, hD, hDLength⟩ :=
    CycleEdgeContact1105.cycle_of_fresh_contacts_to_cycle_edge
      G c u v huv z hz hzu hzv.symm
  have horder : D.length = 2 * d + 1 := by omega
  exact LongCycleOutside1105.no_cycle_of_order_one_below_forbidden_path
    G hconn d hcard hfree D hD horder

/-- Literal ORIGINAL contacts, with no preselected half. -/
def actualContacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (z : V) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun i => G.Adj z (c i))

/-- With actual outside-independence, every actual neighbor of an outsider
lies in the original cycle range; injection then gives the exact degree. -/
theorem contact_card_eq_degree_of_outside_independence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) :
    (actualContacts G c z).card = G.degree z := by
  have himage : (actualContacts G c z).image c = G.neighborFinset z := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
      apply (G.mem_neighborFinset z (c i)).mpr
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      have hadj : G.Adj z v := (G.mem_neighborFinset z v).mp hv
      have hrange : v ∈ Set.range c := by
        by_contra hvOutside
        exact hind z v hz hvOutside hadj
      rcases hrange with ⟨i, rfl⟩
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hadj⟩, rfl⟩
  calc
    (actualContacts G c z).card = ((actualContacts G c z).image c).card :=
      (Finset.card_image_of_injective (actualContacts G c z) c.injective).symm
    _ = G.degree z := by rw [himage, SimpleGraph.card_neighborFinset_eq_degree]

/-- The original degree bound becomes a pointwise successor toggle. The
longer-cycle cap is derived, and the contact count is proved above. Only the
actual outside-independence/support transport remains a conditional premise. -/
theorem actual_contact_card_and_successor_toggle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hconn : G.Connected) (hcard : 2 * d + 2 ≤ Fintype.card V)
    (hmin : ∀ v : V, d ≤ G.degree v)
    (hfree : (pathGraph (2 * d + 2)).Free G)
    {n : ℕ} (c : (cycleGraph (n + 3)).Copy G) (hsize : n + 3 = 2 * d)
    (hind : ∀ x y : V, x ∉ Set.range c → y ∉ Set.range c → ¬G.Adj x y)
    (z : V) (hz : z ∉ Set.range c) :
    (actualContacts G c z).card = d ∧
      ∀ i : Fin (n + 3), G.Adj z (c (i + 1)) ↔ ¬G.Adj z (c i) := by
  let N := actualContacts G c z
  have hdegree : N.card = G.degree z :=
    contact_card_eq_degree_of_outside_independence G c hind z hz
  have hN : d ≤ N.card := by rw [hdegree]; exact hmin z
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

end ErdosProblems.PathUpperReduction.CycleContactCap1105
