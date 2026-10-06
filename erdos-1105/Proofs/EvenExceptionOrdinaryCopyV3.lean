module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Exceptional `H`-family vertex decomposition and ordinary `Copy` adapter on `Fin a ⊕ (Fin 3 ⊕ Fin b)`. -/
namespace ErdosProblems.EvenExceptionExchange
open SimpleGraph

abbrev Vertex (a b : ℕ) := Fin a ⊕ (Fin 3 ⊕ Fin b)
def isA {a b : ℕ} : Vertex a b → Prop
  | .inl _ => True | .inr _ => False
def isC {a b : ℕ} : Vertex a b → Prop
  | .inr (.inl _) => True | _ => False

/-- Literally K_a joined to the disjoint union K_3 and I_b. -/
def familyGraph (a b : ℕ) : SimpleGraph (Vertex a b) where
  Adj x y := x ≠ y ∧ (isA x ∨ isA y ∨ (isC x ∧ isC y))
  symm := by
    refine ⟨?_⟩
    intro x y h; rcases h with ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩
  loopless := by
    refine ⟨?_⟩
    intro x h; exact h.1 rfl

/-- The existing local order-provider interface, now routed to ordinary Copy.
No coloring, maximality, degree hypothesis or graph classification is added. -/
def copy_of_avoiding_order {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (owner : G.edgeSet) (u v : V) (p : Fin (m + 1) → V)
    (hp : Function.Injective p)
    (havoid : ∀ i : Fin m,
      s(p (Fin.castSucc i), p (Fin.succ i)) = s(u, v) ∨
      (G.Adj (p (Fin.castSucc i)) (p (Fin.succ i)) ∧
       s(p (Fin.castSucc i), p (Fin.succ i)) ≠ owner.val)) :
    (pathGraph (m + 1)).Copy
      (G.deleteEdges {owner.val} ⊔ SimpleGraph.fromEdgeSet {s(u, v)}) := by
  let T := G.deleteEdges {owner.val} ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
  have hstep (i : Fin m) : T.Adj (p (Fin.castSucc i)) (p (Fin.succ i)) := by
    rcases havoid i with hnew | ⟨hold, hne⟩
    · apply (SimpleGraph.sup_adj _ _ _ _).mpr
      right
      change s(p (Fin.castSucc i), p (Fin.succ i)) ∈ ({s(u, v)} : Set (Sym2 V)) ∧ p (Fin.castSucc i) ≠ p (Fin.succ i)
      constructor
      · simpa only [Set.mem_singleton_iff] using hnew
      · apply hp.ne
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
    · apply (SimpleGraph.sup_adj _ _ _ _).mpr
      left
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨hold, by simpa only [Set.mem_singleton_iff] using hne⟩
  refine ⟨⟨p, ?_⟩, hp⟩
  intro i j hij
  rcases (pathGraph_adj.mp hij) with h | h
  · have hi : i.val < m := by have hj := j.isLt; omega
    let t : Fin m := ⟨i.val, hi⟩
    have hit : i = Fin.castSucc t := Fin.ext rfl
    have hjt : j = Fin.succ t := Fin.ext (by simpa only [Fin.val_succ] using h.symm)
    simpa only [hit, hjt] using hstep t
  · have hj : j.val < m := by have hi := i.isLt; omega
    let t : Fin m := ⟨j.val, hj⟩
    have hjt : j = Fin.castSucc t := Fin.ext rfl
    have hit : i = Fin.succ t := Fin.ext (by simpa only [Fin.val_succ] using h.symm)
    simpa only [hit, hjt] using T.symm.symm _ _ (hstep t)

end ErdosProblems.EvenExceptionExchange
