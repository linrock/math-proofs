module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Option.Basic
public import Mathlib.Tactic.Abel
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
Arbitrary-host one-apex cone path extraction from a cycle in `cone G`:
rotates a cycle in `cone G` so that deleting the apex yields an injective
`pathGraph` copy in `G` with pointwise support equalities.
-/

namespace ErdosProblems.PathUpperReduction.UniformCone1105

open SimpleGraph

/-- Add one apex, with every old-old adjacency exactly unchanged. -/
def cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a, b with
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a
    · exact id
    · exact G.loopless.irrefl _⟩

/-- The positive, nonwrapping offsets after an apex position. -/
def apexOffset {k m : ℕ} (hkm : k < m) (i : Fin k) : Fin m :=
  ⟨i.val + 1, by omega⟩

/-- The literal first k source vertices of a cycle with at least k vertices. -/
def prefixOffset {k m : ℕ} (hkm : k ≤ m) (i : Fin k) : Fin m :=
  ⟨i.val, by omega⟩

/-- Extract old vertices at actual injective cycle positions. This helper's
positions are constructed in the two following theorems. -/
theorem pathCopy_of_cycle_positions {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} (f : (cycleGraph m).Copy (cone G))
    (q : Fin k → Fin m) (hq : Function.Injective q)
    (hstep : ∀ {a b : Fin k}, a.val + 1 = b.val →
      (cycleGraph m).Adj (q a) (q b))
    (hnotapex : ∀ i, f (q i) ≠ none) :
    ∃ p : (pathGraph k).Copy G, ∀ i, some (p i) = f (q i) := by
  classical
  have hsome (i : Fin k) : ∃ v : V, f (q i) = some v := by
    cases he : f (q i) with
    | none => exact (hnotapex i he).elim
    | some v => exact ⟨v, rfl⟩
  let p : Fin k → V := fun i => Classical.choose (hsome i)
  have hp_eq (i : Fin k) : f (q i) = some (p i) :=
    Classical.choose_spec (hsome i)
  have hp : Function.Injective p := by
    intro a b h
    apply hq
    apply f.injective
    change f (q a) = f (q b)
    rw [hp_eq a, hp_eq b, h]
  have hpstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      G.Adj (p a) (p b) := by
    have hm := f.toHom.map_adj (hstep hab)
    change (cone G).Adj (f (q a)) (f (q b)) at hm
    rw [hp_eq a, hp_eq b] at hm
    exact hm
  let φ : (pathGraph k) →g G := ⟨p, by
    intro a b hab
    rcases pathGraph_adj.mp hab with h | h
    · exact hpstep h
    · exact (hpstep h).symm⟩
  refine ⟨φ.toCopy hp, ?_⟩
  intro i
  exact (hp_eq i).symm

/-- When this actual cycle contains the apex, select its k old vertices
immediately after that apex. The cycle need not span the host. -/
theorem pathCopy_of_cycle_with_apex {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} [NeZero m] (hkm : k < m)
    (f : (cycleGraph m).Copy (cone G)) (j : Fin m) (hj : f j = none) :
    ∃ p : (pathGraph k).Copy G,
      ∀ i, some (p i) = f (j + apexOffset hkm i) := by
  classical
  let d : Fin k → Fin m := apexOffset hkm
  let q : Fin k → Fin m := fun i => j + d i
  have hd : Function.Injective d := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change a.val + 1 = b.val + 1 at hv
    omega
  have hq : Function.Injective q := by
    intro a b h
    apply hd
    exact add_left_cancel h
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      (cycleGraph m).Adj (q a) (q b) := by
    have hle : d a ≤ d b := by
      change a.val + 1 ≤ b.val + 1
      omega
    have hsub : (d b - d a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      change (b.val + 1) - (a.val + 1) = 1
      omega
    have hrot : (q b - q a).val = 1 := by
      have heq : q b - q a = d b - d a := by
        dsimp [q]
        abel
      rw [heq]
      exact hsub
    exact cycleGraph_adj'.mpr (Or.inr hrot)
  have hnotapex (i : Fin k) : f (q i) ≠ none := by
    intro hi
    have hqi : q i = j := f.injective (hi.trans hj.symm)
    have hz : d i = (0 : Fin m) := by
      apply add_left_cancel (a := j)
      simpa only [q, add_zero] using hqi
    have hv := congrArg Fin.val hz
    have hbad : i.val + 1 = 0 := by
      simpa only [d, apexOffset, Fin.val_zero] using hv
    omega
  exact pathCopy_of_cycle_positions G f q hq (fun h => hstep h) hnotapex

/-- When this actual cycle avoids the apex, select its first k vertices. -/
theorem pathCopy_of_cycle_without_apex {V : Type*} (G : SimpleGraph V)
    {k m : ℕ} (hkm : k ≤ m) (f : (cycleGraph m).Copy (cone G))
    (hnotapex : ∀ j, f j ≠ none) :
    ∃ p : (pathGraph k).Copy G,
      ∀ i, some (p i) = f (prefixOffset hkm i) := by
  classical
  let q : Fin k → Fin m := prefixOffset hkm
  have hq : Function.Injective q := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) h
  have hstep {a b : Fin k} (hab : a.val + 1 = b.val) :
      (cycleGraph m).Adj (q a) (q b) := by
    have hle : q a ≤ q b := by
      change a.val ≤ b.val
      omega
    have hsub : (q b - q a).val = 1 := by
      rw [Fin.sub_val_of_le hle]
      change b.val - a.val = 1
      omega
    exact cycleGraph_adj'.mpr (Or.inr hsub)
  exact pathCopy_of_cycle_positions G f q hq (fun h => hstep h)
    (fun i => hnotapex (q i))

/-- On any host carrier, ordinary P_k freedom excludes every cycle of
order at least k+1 in the faithful one-apex cone. -/
theorem cone_all_long_cycle_free {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 5 ≤ k) (hfree : (pathGraph k).Free G) :
    ∀ m, k + 1 ≤ m → (cycleGraph m).Free (cone G) := by
  classical
  intro m hm hcopy
  obtain ⟨f⟩ := hcopy
  have hm6 : 6 ≤ m := le_trans (Nat.add_le_add_right hk 1) hm
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 6) hm6
  let : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hkm : k < m := by omega
  by_cases ha : ∃ j, f j = none
  · obtain ⟨j, hj⟩ := ha
    obtain ⟨p, _⟩ := pathCopy_of_cycle_with_apex G hkm f j hj
    exact hfree ⟨p⟩
  · have hnotapex : ∀ j, f j ≠ none := by
      intro j hj
      exact ha ⟨j, hj⟩
    obtain ⟨p, _⟩ := pathCopy_of_cycle_without_apex G (Nat.le_of_lt hkm) f hnotapex
    exact hfree ⟨p⟩

/-- Literal finite-host FC1105 domain; no spanning or apex-range premise. -/
theorem finite_cone_all_long_cycle_free {n k : ℕ} (G : SimpleGraph (Fin n))
    (_hkn : k ≤ n) (hk : 5 ≤ k) (hfree : (pathGraph k).Free G) :
    ∀ m, k + 1 ≤ m → (cycleGraph m).Free (cone G) :=
  cone_all_long_cycle_free G hk hfree

end ErdosProblems.PathUpperReduction.UniformCone1105
