module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

@[expose] public section

/-!
# Cutting an actual cycle with both path endpoints retained

Cuts a `SimpleGraph.Copy (cycleGraph (n + 3)) G` across a cycle edge to obtain
a spanning `pathGraph (n + 3)` copy while tracking both endpoint indices.
-/

namespace ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105

open SimpleGraph

theorem last_eq_neg_one (n : ℕ) :
    (Fin.last (n + 2) : Fin (n + 3)) = -1 := by
  apply Fin.ext
  simp only [Fin.val_last, Fin.coe_neg_one]

theorem no_wrap_path_edge (n : ℕ) :
    ¬(pathGraph (n + 3)).Adj (-1) 0 ∧ ¬(pathGraph (n + 3)).Adj 0 (-1) := by
  constructor <;> intro h <;> rcases pathGraph_adj.mp h with h | h <;>
    simp only [Fin.coe_neg_one, Fin.val_zero] at h <;> omega

def path_copy_avoiding {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (old : Sym2 V) (q : Fin (n + 3) → V) (hq : Function.Injective q)
    (hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j))
    (ha : ∀ i j, (pathGraph (n + 3)).Adj i j → s(q i, q j) ≠ old) :
    (pathGraph (n + 3)).Copy (G.deleteEdges {old}) :=
  ⟨⟨q, by
    intro i j hij
    exact deleteEdges_adj.mpr
      ⟨hm i j hij, by simpa only [Set.mem_singleton_iff] using ha i j hij⟩⟩, hq⟩

theorem shift_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa only [add_sub_add_right_eq_sub] using h

theorem reverse_cycle_adj (n : ℕ) (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (r - i) (r - j) := by
  have h₁ : (r - i) - (r - j) = j - i := by abel
  have h₂ : (r - j) - (r - i) = i - j := by abel
  rw [cycleGraph_adj'] at h ⊢
  simpa only [h₁, h₂, or_comm] using h

/-- The forward order begins at `c r` and ends at its actual predecessor. -/
theorem path_of_cycle_cut_predecessor_at_both_ends {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c (r - 1), c r)}),
      p 0 = c r ∧ p (Fin.last (n + 2)) = c (r - 1) ∧
        Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (i + r)
  have hq : Function.Injective q := by
    intro i j h
    exact add_right_cancel (c.injective h)
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (shift_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c (r - 1), c r) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = (i + r) - r := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = (j + r) - r := by abel
             _ = (r - 1) - r := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_, ?_⟩
  · change c (0 + r) = c r
    rw [zero_add]
  · change c (Fin.last (n + 2) + r) = c (r - 1)
    rw [last_eq_neg_one]
    congr 1
    abel
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - r, ?_⟩
      change c (i - r + r) = c i
      rw [sub_add_cancel]

/-- The reverse order begins at `c r` and ends at its actual successor. -/
theorem path_of_cycle_cut_successor_at_both_ends {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G) (r : Fin (n + 3)) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c r, c (r + 1))}),
      p 0 = c r ∧ p (Fin.last (n + 2)) = c (r + 1) ∧
        Set.range p = Set.range c := by
  classical
  let q : Fin (n + 3) → V := fun i => c (r - i)
  have hq : Function.Injective q := by
    intro i j h
    have he := c.injective h
    calc i = r - (r - i) := by abel
         _ = r - (r - j) := by rw [he]
         _ = j := by abel
  have hm : ∀ i j, (pathGraph (n + 3)).Adj i j → G.Adj (q i) (q j) := by
    intro i j hij
    exact c.toHom.map_rel' (reverse_cycle_adj n r i j (pathGraph_le_cycleGraph hij))
  have ha : ∀ i j, (pathGraph (n + 3)).Adj i j →
      s(q i, q j) ≠ s(c r, c (r + 1)) := by
    intro i j hij he
    rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 0 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      have hj' : j = -1 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      exact (no_wrap_path_edge n).2 (by simpa only [hi', hj'] using hij)
    · have hi' : i = -1 := by
        have h := c.injective hi
        calc i = r - (r - i) := by abel
             _ = r - (r + 1) := by rw [h]
             _ = -1 := by abel
      have hj' : j = 0 := by
        have h := c.injective hj
        calc j = r - (r - j) := by abel
             _ = r - r := by rw [h]
             _ = 0 := by abel
      exact (no_wrap_path_edge n).1 (by simpa only [hi', hj'] using hij)
  refine ⟨path_copy_avoiding G _ q hq hm ha, ?_, ?_, ?_⟩
  · change c (r - 0) = c r
    rw [sub_zero]
  · change c (r - Fin.last (n + 2)) = c (r + 1)
    rw [last_eq_neg_one]
    congr 1
    abel
  · change Set.range q = Set.range c
    ext v
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨r - i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨r - i, ?_⟩
      change c (r - (r - i)) = c i
      congr 1
      abel

/-- Cutting any actual cycle edge retains the prescribed ordered endpoints. -/
theorem path_of_cycle_cut_edge_at_both_endpoints {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (c : (cycleGraph (n + 3)).Copy G)
    (u v : Fin (n + 3)) (huv : (cycleGraph (n + 3)).Adj u v) :
    ∃ p : (pathGraph (n + 3)).Copy (G.deleteEdges {s(c u, c v)}),
      p 0 = c u ∧ p (Fin.last (n + 2)) = c v ∧
        Set.range p = Set.range c := by
  classical
  rcases cycleGraph_adj'.mp huv with h | h
  · have hdiff : u - v = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u - 1 := by
      have he := sub_eq_iff_eq_add.mp hdiff
      calc v = (1 + v) - 1 := by abel
           _ = u - 1 := by rw [← he]
    have he : s(c (u - 1), c u) = s(c u, c v) := by
      rw [hv]
      exact Sym2.eq_swap
    rw [← he, hv]
    exact path_of_cycle_cut_predecessor_at_both_ends G c u
  · have hdiff : v - u = (1 : Fin (n + 3)) := by
      apply Fin.ext
      simpa only [Fin.val_one] using h
    have hv : v = u + 1 := by
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hdiff)
    rw [hv]
    exact path_of_cycle_cut_successor_at_both_ends G c u

end ErdosProblems.PathUpperReduction.CycleCutBothEndpoints1105
