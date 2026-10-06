module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Tactic

@[expose] public section

/-!
The edges of a non-induced `cycleGraph (m+1)` are exactly the `m`
consecutive edges and one closing edge. This indexed classification is
the graph-only source-edge layer for a later rainbow host Copy.
-/

namespace ErdosProblems.AntiRamseyCycleOrderedEdges

open SimpleGraph

theorem cycle_adj_cases {m : ℕ} (_hm : 2 ≤ m)
    {a b : Fin (m + 1)} (hab : (cycleGraph (m + 1)).Adj a b) :
    a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
      (a.val = 0 ∧ b.val = m) ∨
      (b.val = 0 ∧ a.val = m) := by
  rw [cycleGraph_adj'] at hab
  rcases hab with h | h
  · by_cases hle : b ≤ a
    · have hsub : (a - b).val = a.val - b.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      right; left
      omega
    · have hlt : a < b := lt_of_not_ge hle
      have hsub : (a - b).val = m + 1 + a.val - b.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have hb := b.isLt
      right; right; left
      omega
  · by_cases hle : a ≤ b
    · have hsub : (b - a).val = b.val - a.val := Fin.sub_val_of_le hle
      rw [hsub] at h
      left
      omega
    · have hlt : b < a := lt_of_not_ge hle
      have hsub : (b - a).val = m + 1 + b.val - a.val :=
        Fin.coe_sub_iff_lt.mpr hlt
      rw [hsub] at h
      have ha := a.isLt
      right; right; right
      omega

/-- The source edge between the consecutive positions `i` and `i+1`. -/
def sourceStep {m : ℕ} (i : Fin m) : (cycleGraph (m + 1)).edgeSet :=
  ⟨s(Fin.castSucc i, Fin.succ i), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    apply pathGraph_le_cycleGraph
    rw [pathGraph_adj]
    left
    simp only [Fin.val_castSucc, Fin.val_succ]⟩

/-- The source edge from the final position back to zero. -/
def sourceClosing (m : ℕ) (_hm : 2 ≤ m) :
    (cycleGraph (m + 1)).edgeSet :=
  ⟨s((0 : Fin (m + 1)), Fin.last m), by
    apply (SimpleGraph.mem_edgeSet _).mpr
    rw [cycleGraph_adj']
    left
    have hlt : (0 : Fin (m + 1)) < Fin.last m := by
      simp [Fin.lt_def, Fin.val_last]
      omega
    rw [Fin.coe_sub_iff_lt.mpr hlt]
    simp only [Fin.val_zero, Fin.val_last]
    omega⟩

/-- Consecutive source edges have different indices. -/
theorem sourceStep_injective {m : ℕ} :
    Function.Injective (sourceStep (m := m)) := by
  intro i j hij
  have hv := congrArg Subtype.val hij
  change s(Fin.castSucc i, Fin.succ i) =
    s(Fin.castSucc j, Fin.succ j) at hv
  rcases (Sym2.eq_iff.mp hv) with h | h
  · exact Fin.castSucc_injective m h.1
  · have hi := congrArg Fin.val h.1
    have hj := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ] at hi hj
    have hii := i.isLt
    have hjj := j.isLt
    omega

/-- The closing edge is not any consecutive edge for cycles of length
at least three. -/
theorem sourceStep_ne_closing {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    sourceStep i ≠ sourceClosing m hm := by
  intro heq
  have hv := congrArg Subtype.val heq
  change s(Fin.castSucc i, Fin.succ i) =
    s((0 : Fin (m + 1)), Fin.last m) at hv
  rcases (Sym2.eq_iff.mp hv) with h | h
  · have h0 := congrArg Fin.val h.1
    have hlast := congrArg Fin.val h.2
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero,
      Fin.val_last] at h0 hlast
    omega
  · have hlast := congrArg Fin.val h.1
    simp only [Fin.val_castSucc, Fin.val_last] at hlast
    have hi := i.isLt
    omega

/-- Every edge of the literal source cycle is a consecutive edge or
its closing edge. No induced-copy assumption is used. -/
theorem sourceEdge_cases {m : ℕ} (hm : 2 ≤ m)
    (e : (cycleGraph (m + 1)).edgeSet) :
    (∃ i : Fin m, e = sourceStep i) ∨ e = sourceClosing m hm := by
  obtain ⟨q, hq⟩ := e
  induction q using Sym2.inductionOn with
  | _ a b =>
    have hab : (cycleGraph (m + 1)).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp hq
    rcases cycle_adj_cases hm hab with hsucc | hsucc | hclose | hclose
    · have hi : a.val < m := by
        have hb := b.isLt
        omega
      let i : Fin m := ⟨a.val, hi⟩
      have ha : a = Fin.castSucc i := Fin.ext (by rfl)
      have hb : b = Fin.succ i := Fin.ext (by
        simp only [Fin.val_succ, i]
        exact hsucc.symm)
      left
      refine ⟨i, ?_⟩
      apply Subtype.ext
      change s(a, b) = s(Fin.castSucc i, Fin.succ i)
      rw [ha, hb]
    · have hi : b.val < m := by
        have ha := a.isLt
        omega
      let i : Fin m := ⟨b.val, hi⟩
      have hb : b = Fin.castSucc i := Fin.ext (by rfl)
      have ha : a = Fin.succ i := Fin.ext (by
        simp only [Fin.val_succ, i]
        exact hsucc.symm)
      left
      refine ⟨i, ?_⟩
      apply Subtype.ext
      change s(a, b) = s(Fin.castSucc i, Fin.succ i)
      rw [ha, hb]
      exact Sym2.eq_swap
    · have ha : a = (0 : Fin (m + 1)) :=
        Fin.ext (by simpa using hclose.1)
      have hb : b = Fin.last m :=
        Fin.ext (by simpa only [Fin.val_last] using hclose.2)
      right
      apply Subtype.ext
      change s(a, b) = s((0 : Fin (m + 1)), Fin.last m)
      rw [ha, hb]
    · have hb : b = (0 : Fin (m + 1)) :=
        Fin.ext (by simpa using hclose.1)
      have ha : a = Fin.last m :=
        Fin.ext (by simpa only [Fin.val_last] using hclose.2)
      right
      apply Subtype.ext
      change s(a, b) = s((0 : Fin (m + 1)), Fin.last m)
      rw [ha, hb]
      exact Sym2.eq_swap

end ErdosProblems.AntiRamseyCycleOrderedEdges
