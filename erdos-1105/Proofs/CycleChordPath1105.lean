module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.SplitIfs
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
One ORIGINAL chord in an actual indexed cycle gives a spanning ORIGINAL path
whose two endpoints are the successors of the chord endpoints. The path
order, injectivity, complete range and both endpoints are constructed here;
none is a premise. The chord endpoints may be consecutive.

This is the two-cut/rejoin step needed to exclude a chord inside the
noncontacted cycle half. Attaching the two distinct outside vertices is a
separate existing/parent-owned endpoint application.
-/

namespace ErdosProblems.PathUpperReduction.CycleChordPath1105

open SimpleGraph

/-- In coordinates rooted at the first chord endpoint, the order is
`1,...,t,0,m-1,...,t+1`. -/
def chordOrder {n : ℕ} (t i : Fin (n + 3)) : Fin (n + 3) :=
  if h : i.val < t.val then
    ⟨i.val + 1, by have ht := t.isLt; omega⟩
  else if he : i.val = t.val then 0
  else
    ⟨n + 3 + t.val - i.val, by
      have hi := i.isLt
      have ht := t.isLt
      omega⟩

theorem chordOrder_val {n : ℕ} (t i : Fin (n + 3)) :
    (chordOrder t i).val =
      if i.val < t.val then i.val + 1
      else if i.val = t.val then 0
      else n + 3 + t.val - i.val := by
  by_cases h : i.val < t.val
  · simp only [chordOrder, dite_eq_left h, ite_eq_left h]
  · by_cases he : i.val = t.val
    · simp only [chordOrder, dite_eq_right h, dite_eq_left he,
        ite_eq_right h, ite_eq_left he, Fin.val_zero]
    · simp only [chordOrder, dite_eq_right h, dite_eq_right he,
        ite_eq_right h, ite_eq_right he]

theorem chordOrder_injective {n : ℕ} (t : Fin (n + 3)) :
    Function.Injective (chordOrder t) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [chordOrder_val, chordOrder_val] at hv
  have ha := a.isLt
  have hb := b.isLt
  have ht := t.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem chordOrder_surjective {n : ℕ} (t : Fin (n + 3)) :
    Function.Surjective (chordOrder t) := by
  intro l
  by_cases hz : l.val = 0
  · refine ⟨t, ?_⟩
    apply Fin.ext
    rw [chordOrder_val]
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    exact hz.symm
  · by_cases hl : l.val ≤ t.val
    · let k : Fin (n + 3) := ⟨l.val - 1, by have h := l.isLt; omega⟩
      have hk : k.val < t.val := by dsimp [k]; omega
      refine ⟨k, ?_⟩
      apply Fin.ext
      rw [chordOrder_val, ite_eq_left hk]
      dsimp [k]
      omega
    · let k : Fin (n + 3) :=
        ⟨n + 3 + t.val - l.val, by
          have h := l.isLt
          have ht := t.isLt
          omega⟩
      have hk : ¬k.val < t.val := by dsimp [k]; have h := l.isLt; omega
      have hkne : k.val ≠ t.val := by dsimp [k]; have h := l.isLt; omega
      refine ⟨k, ?_⟩
      apply Fin.ext
      rw [chordOrder_val, ite_eq_right hk, ite_eq_right hkne]
      dsimp [k]
      have h := l.isLt
      have ht := t.isLt
      omega

theorem chordOrder_zero {n : ℕ} (t : Fin (n + 3))
    (ht : 0 < t.val) : chordOrder t 0 = 1 := by
  have hpos : (0 : Fin (n + 3)).val < t.val := ht
  apply Fin.ext
  rw [chordOrder_val, ite_eq_left hpos]
  simp only [Fin.val_zero, Fin.val_one]

theorem chordOrder_last {n : ℕ} (t : Fin (n + 3)) :
    chordOrder t (Fin.last (n + 2)) = t + 1 := by
  have ht := t.isLt
  have hnlt : ¬n + 2 < t.val := by omega
  by_cases he : t.val = n + 2
  · have hq : (chordOrder t (Fin.last (n + 2))).val = 0 := by
      rw [chordOrder_val]
      simp only [Fin.val_last, ite_eq_right hnlt, ite_eq_left he.symm]
    apply Fin.ext
    rw [hq, Fin.val_add]
    simp only [Fin.val_one]
    rw [he]
    have hsum : n + 2 + 1 = n + 3 := by omega
    rw [hsum, Nat.mod_self]
  · have hq : (chordOrder t (Fin.last (n + 2))).val = t.val + 1 := by
      rw [chordOrder_val]
      simp only [Fin.val_last, ite_eq_right hnlt, ite_eq_right (Ne.symm he)]
      omega
    apply Fin.ext
    rw [hq, Fin.val_add_eq_of_add_lt]
    · simp only [Fin.val_one]
    · simp only [Fin.val_one]
      omega

theorem shifted_cycle_adj {n : ℕ} (r i j : Fin (n + 3))
    (h : (cycleGraph (n + 3)).Adj i j) :
    (cycleGraph (n + 3)).Adj (i + r) (j + r) := by
  rw [cycleGraph_adj'] at h ⊢
  simpa only [add_sub_add_right_eq_sub] using h

theorem original_successive_adj {V : Type*} {n : ℕ}
    {G : SimpleGraph V} (c : (cycleGraph (n + 3)).Copy G)
    {a b : Fin (n + 3)} (hab : a.val + 1 = b.val) :
    G.Adj (c a) (c b) :=
  c.toHom.map_rel' (pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl hab)))

theorem chordOrder_successive_adj {V : Type*} {n : ℕ}
    {G : SimpleGraph V} (c : (cycleGraph (n + 3)).Copy G)
    (t : Fin (n + 3)) (hchord : G.Adj (c t) (c 0))
    {a b : Fin (n + 3)} (hab : a.val + 1 = b.val) :
    G.Adj (c (chordOrder t a)) (c (chordOrder t b)) := by
  have haLt := a.isLt
  have hbLt := b.isLt
  have htLt := t.isLt
  by_cases ha : a.val < t.val
  · by_cases hb : b.val < t.val
    · apply original_successive_adj c
      rw [chordOrder_val, chordOrder_val, ite_eq_left ha, ite_eq_left hb]
      omega
    · have hbe : b.val = t.val := by omega
      have hqa : chordOrder t a = t := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_left ha]
        omega
      have hqb : chordOrder t b = 0 := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right hb, ite_eq_left hbe]
        rfl
      rw [hqa, hqb]
      exact hchord
  · have hb : ¬b.val < t.val := by omega
    by_cases hae : a.val = t.val
    · have hbne : b.val ≠ t.val := by omega
      have hqa : chordOrder t a = 0 := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right ha, ite_eq_left hae]
        rfl
      have hqb : chordOrder t b = Fin.last (n + 2) := by
        apply Fin.ext
        rw [chordOrder_val, ite_eq_right hb, ite_eq_right hbne]
        simp only [Fin.val_last]
        omega
      rw [hqa, hqb]
      apply c.toHom.map_rel'
      simp [cycleGraph_adj]
    · have hbne : b.val ≠ t.val := by omega
      apply SimpleGraph.Adj.symm
      apply original_successive_adj c
      rw [chordOrder_val, chordOrder_val, ite_eq_right hb, ite_eq_right hbne,
        ite_eq_right ha, ite_eq_right hae]
      omega

/-- The actual chord endpoints determine the path internally.  Both endpoints
and the entire original cycle population are certified in the conclusion. -/
theorem path_of_actual_cycle_chord {V : Type*} {n : ℕ} (G : SimpleGraph V)
    (c : (cycleGraph (n + 3)).Copy G) (r s : Fin (n + 3))
    (hrs : r ≠ s) (hchord : G.Adj (c r) (c s)) :
    ∃ p : (pathGraph (n + 3)).Copy G,
      p 0 = c (r + 1) ∧
      p (Fin.last (n + 2)) = c (s + 1) ∧
      Set.range p = Set.range c := by
  classical
  let f : (cycleGraph (n + 3)) →g G :=
    ⟨fun i => c (i + r), fun hab => c.toHom.map_rel' (shifted_cycle_adj r _ _ hab)⟩
  have hf : Function.Injective f := by
    intro i j h
    change c (i + r) = c (j + r) at h
    exact add_right_cancel (c.injective h)
  let c' := f.toCopy hf
  let t : Fin (n + 3) := s - r
  have htne : t ≠ 0 := by
    change s - r ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hrs)
  have htpos : 0 < t.val := by
    have h : t.val ≠ 0 := by
      intro he
      apply htne
      apply Fin.ext
      simpa only [Fin.val_zero] using he
    omega
  have hchord' : G.Adj (c' t) (c' 0) := by
    change G.Adj (c ((s - r) + r)) (c (0 + r))
    simpa only [sub_add_cancel, zero_add] using hchord.symm
  let h : (pathGraph (n + 3)) →g G :=
    ⟨fun i => c' (chordOrder t i), by
      intro i j hij
      rcases pathGraph_adj.mp hij with hij | hji
      · exact chordOrder_successive_adj c' t hchord' hij
      · exact (chordOrder_successive_adj c' t hchord' hji).symm⟩
  have hinj : Function.Injective h := by
    intro i j hij
    exact chordOrder_injective t (c'.injective hij)
  let p := h.toCopy hinj
  refine ⟨p, ?_, ?_, ?_⟩
  · change c ((chordOrder t 0) + r) = c (r + 1)
    rw [chordOrder_zero t htpos]
    exact congrArg c (add_comm (1 : Fin (n + 3)) r)
  · change c ((chordOrder t (Fin.last (n + 2))) + r) = c (s + 1)
    rw [chordOrder_last]
    change c ((s - r + 1) + r) = c (s + 1)
    congr 1
    abel
  · ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨chordOrder t i + r, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := chordOrder_surjective t (i - r)
      refine ⟨k, ?_⟩
      change c (chordOrder t k + r) = c i
      rw [hk, sub_add_cancel]

end ErdosProblems.PathUpperReduction.CycleChordPath1105
