module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

/-!
Definitions `cycleLengths` and `oddCycleLengths` follow the Apache-2.0
Formal Conjectures Authors' Circumference.lean (2026).
-/

namespace SimpleGraph

def cycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m | ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

end SimpleGraph

namespace Erdos58

/-- The properties of a finite normal DFS forest needed by the coloring proof.
They require actual simple graph paths, not merely numerical depth labels. -/
structure NormalDepth {V : Type*} (G : SimpleGraph V) where
  depth : V → ℕ
  edge_ne : ∀ {u v}, G.Adj u v → depth u ≠ depth v
  earlier_injective : ∀ {v u w}, G.Adj u v → G.Adj w v →
    depth u < depth v → depth w < depth v → depth u = depth w → u = w
  back_path : ∀ {u v}, G.Adj u v → depth u < depth v →
    ∃ p : G.Walk u v, p.IsPath ∧ p.length = depth v - depth u

end Erdos58
