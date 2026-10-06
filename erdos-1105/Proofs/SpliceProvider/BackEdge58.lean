module

public import SpliceProvider.OddCycle58

@[expose] public section

namespace Erdos58

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Closing a simple path of length at least two by an edge gives a cycle. -/
theorem cycle_of_path_and_edge {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (h : G.Adj v u) (hlen : 2 ≤ p.length) :
    (Walk.cons h p).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simpa using hp
  · simp only [Walk.length_cons]
    omega

/-- An edge between vertices of equal depth parity closes an actual odd cycle. -/
theorem same_parity_back_edge (D : NormalDepth G) {u v : V}
    (h : G.Adj u v) (hlt : D.depth u < D.depth v)
    (hpar : D.depth u % 2 = D.depth v % 2) :
    D.depth v - D.depth u + 1 ∈ G.oddCycleLengths := by
  obtain ⟨p, hp, hlen⟩ := D.back_path h hlt
  have htwo : 2 ≤ p.length := by omega
  refine ⟨⟨v, Walk.cons h.symm p,
    cycle_of_path_and_edge p hp h.symm htwo, ?_⟩, ?_⟩
  · simp [hlen]
  · rw [Nat.odd_iff]
    omega

def earlierParityNeighbors (D : NormalDepth G) (v : V) : Set V :=
  {u | G.Adj u v ∧ D.depth u < D.depth v ∧ D.depth u % 2 = D.depth v % 2}

/-- Earlier same-parity neighbors inject into the set of odd cycle lengths. -/
theorem earlier_parity_neighbors_bound [Finite V] (D : NormalDepth G)
    (hfin : G.oddCycleLengths.Finite) (v : V) :
    (earlierParityNeighbors D v).ncard ≤ G.oddCycleLengths.ncard := by
  classical
  let f : V → ℕ := fun u ↦ D.depth v - D.depth u + 1
  have hmaps : Set.MapsTo f (earlierParityNeighbors D v) G.oddCycleLengths := by
    intro u hu
    exact same_parity_back_edge D hu.1 hu.2.1 hu.2.2
  have hinj : Set.InjOn f (earlierParityNeighbors D v) := by
    intro u hu w hw heq
    apply D.earlier_injective hu.1 hw.1 hu.2.1 hw.2.1
    dsimp [f] at heq
    have hu_lt : D.depth u < D.depth v := hu.2.1
    have hw_lt : D.depth w < D.depth v := hw.2.1
    omega
  exact Set.ncard_le_ncard_of_injOn f hmaps hinj hfin

end Erdos58
