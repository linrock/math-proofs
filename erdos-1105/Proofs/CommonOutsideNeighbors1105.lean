module

public import CycleCutBothEndpoints1105
public import EndpointAttachment1105

@[expose] public section

/-!
# Agreement of actual outside contact sets

The final auxiliary explicitly assumes per-outsider successor toggles. The
full graph caller must derive those from actual index finsets, degree counts,
and the no-consecutive-contact argument. It must also supply an actual cycle,
two distinct actual outside vertices, and literal path freedom. No completed
graph, favorable rotation, supplied path, or desired agreement is assumed.
-/

namespace ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105

open SimpleGraph
open ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105
open ErdosProblems.PathUpperReduction.EndpointAttachment1105

/-- Opposite contacts at an actual consecutive cycle edge would produce the
forbidden path on all cycle vertices plus the two actual outsiders. -/
theorem successor_contacts_incompatible_of_free {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c)
    (hne : u ≠ v) (i : Fin (n + 3)) :
    ¬(G.Adj u (c i) ∧ G.Adj v (c (i + 1))) := by
  classical
  have hi : (cycleGraph (n + 3)).Adj i (i + 1) :=
    cycleGraph_adj.mpr (Or.inr (by abel))
  obtain ⟨p, hp0, hplast, hprange⟩ :=
    path_of_cycle_cut_edge_at_both_endpoints G c i (i + 1) hi
  let P : (pathGraph (n + 3)).Copy G :=
    ⟨⟨p, by
      intro a b hab
      exact (deleteEdges_adj.mp (p.toHom.map_rel' hab)).1⟩, p.injective⟩
  have hP0 : P 0 = c i := by
    change p 0 = c i
    exact hp0
  have hPlast : P (Fin.last (n + 2)) = c (i + 1) := by
    change p (Fin.last (n + 2)) = c (i + 1)
    exact hplast
  have hPrange : Set.range P = Set.range c := by
    change Set.range p = Set.range c
    exact hprange
  have huP : u ∉ Set.range P := by
    rw [hPrange]
    exact hu
  have hvP : v ∉ Set.range P := by
    rw [hPrange]
    exact hv
  rintro ⟨hui, hvi⟩
  apply endpoint_contacts_incompatible_of_free G (n + 2) hfree P u v huP hvP hne
  constructor
  · simpa only [hP0] using hui
  · simpa only [hPlast] using hvi.symm

/-- Derived per-outsider alternation forces the SAME actual cycle contact set.
The toggles are explicit intermediate hypotheses, to be derived by the graph
caller; no parity half or common-contact-set oracle is supplied. -/
theorem outside_contact_sets_agree_of_toggles {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (hfree : (pathGraph (n + 5)).Free G)
    (u v : V) (hu : u ∉ Set.range c) (hv : v ∉ Set.range c)
    (hne : u ≠ v)
    (htoggleu : ∀ i : Fin (n + 3), G.Adj u (c (i + 1)) ↔ ¬G.Adj u (c i))
    (htogglev : ∀ i : Fin (n + 3), G.Adj v (c (i + 1)) ↔ ¬G.Adj v (c i)) :
    {i : Fin (n + 3) | G.Adj u (c i)} =
      {i : Fin (n + 3) | G.Adj v (c i)} := by
  classical
  ext i
  change G.Adj u (c i) ↔ G.Adj v (c i)
  constructor
  · intro hui
    by_contra hnvi
    have hvs : G.Adj v (c (i + 1)) := (htogglev i).mpr hnvi
    exact (successor_contacts_incompatible_of_free G c hfree u v hu hv hne i)
      ⟨hui, hvs⟩
  · intro hvi
    by_contra hnui
    have hus : G.Adj u (c (i + 1)) := (htoggleu i).mpr hnui
    exact (successor_contacts_incompatible_of_free G c hfree v u hv hu hne.symm i)
      ⟨hvi, hus⟩

end ErdosProblems.PathUpperReduction.CommonOutsideNeighbors1105
