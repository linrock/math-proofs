module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.Pairwise
public import Mathlib.Tactic

@[expose] public section

/-!
Finite greedy interval selection. The returned list is constructed from cut coverage; no vine or order is assumed. The recursive certificate records every selected interval, maximum right end,
minimum-left tie, strict progress and the preceding-but-one separation. No graph detour, disjoint ear support or cycle construction is claimed here.
-/

namespace ErdosProblems.PathUpperReduction.IntervalVine

abbrev Interval := ℕ × ℕ

def Valid (F : Finset Interval) (s : ℕ) : Prop :=
  ∀ p ∈ F, p.1 < p.2 ∧ p.2 ≤ s

def Cuts (F : Finset Interval) (s : ℕ) : Prop :=
  ∀ c, 0 < c → c < s → ∃ p ∈ F, p.1 < c ∧ c < p.2

def RightBound (F : Finset Interval) (previous reach : ℕ) : Prop :=
  ∀ p ∈ F, p.1 < previous → p.2 ≤ reach

/-- Maximum right end, with minimum left end among its ties. -/
theorem exists_right_max_left_min (S : Finset Interval) (hS : S.Nonempty) :
    ∃ p ∈ S, (∀ q ∈ S, q.2 ≤ p.2) ∧
      (∀ q ∈ S, q.2 = p.2 → p.1 ≤ q.1) := by
  classical
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun q => q.2) hS
  let T := S.filter (fun q => q.2 = p.2)
  have hT : T.Nonempty := ⟨p, by simp [T, hp]⟩
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image T (fun q => q.1) hT
  have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
  have hqp : q.2 = p.2 := (Finset.mem_filter.mp hq).2
  refine ⟨q, hqS, ?_, ?_⟩
  · intro v hv
    rw [hqp]
    exact hmax v hv
  · intro v hv hvq
    apply hmin v
    exact Finset.mem_filter.mpr ⟨hv, hvq.trans hqp⟩

/-- One exact greedy extension. Its previous bound is propagated, and its
selected left end cannot lie below the preceding reach. -/
theorem exists_greedy_step (F : Finset Interval) (s previous reach : ℕ)
    (hvalid : Valid F s) (hcuts : Cuts F s)
    (hpositive : 0 < reach) (hless : reach < s)
    (hinvariant : RightBound F previous reach) :
    ∃ p ∈ F, previous ≤ p.1 ∧ p.1 < reach ∧ reach < p.2 ∧ p.2 ≤ s ∧
      RightBound F reach p.2 ∧
      (∀ q ∈ F, q.1 < reach → q.2 = p.2 → p.1 ≤ q.1) := by
  classical
  obtain ⟨cross, hcrossF, hcrossL, hcrossR⟩ := hcuts reach hpositive hless
  let S := F.filter (fun q => q.1 < reach)
  have hS : S.Nonempty := ⟨cross, Finset.mem_filter.mpr ⟨hcrossF, hcrossL⟩⟩
  obtain ⟨p, hpS, hmax, hmin⟩ := exists_right_max_left_min S hS
  have hpF : p ∈ F := (Finset.mem_filter.mp hpS).1
  have hpL : p.1 < reach := (Finset.mem_filter.mp hpS).2
  have hpR : reach < p.2 :=
    lt_of_lt_of_le hcrossR (hmax cross (Finset.mem_filter.mpr ⟨hcrossF, hcrossL⟩))
  have hprevious : previous ≤ p.1 := by
    by_contra hnot
    have hsmall : p.1 < previous := by omega
    have hbound := hinvariant p hpF hsmall
    omega
  refine ⟨p, hpF, hprevious, hpL, hpR, (hvalid p hpF).2, ?_, ?_⟩
  · intro q hq hqL
    exact hmax q (Finset.mem_filter.mpr ⟨hq, hqL⟩)
  · intro q hq hqL hqR
    exact hmin q (Finset.mem_filter.mpr ⟨hq, hqL⟩) hqR

/-- A literal list certificate. After an interval with right end `reach`,
the next interval starts before `reach` and at or above `previous`; recursively
the pair of reaches becomes `(reach,newRight)`. Thus its third selected left
end is at least the first selected right end, and so on. -/
inductive GreedyTail (F : Finset Interval) (s : ℕ) :
    ℕ → ℕ → List Interval → Prop
  | done (previous : ℕ) : GreedyTail F s previous s []
  | step (previous reach : ℕ) (p : Interval) (rest : List Interval)
      (hp : p ∈ F) (hprevious : previous ≤ p.1) (hleft : p.1 < reach)
      (hadvance : reach < p.2) (hbound : p.2 ≤ s)
      (hmaximum : RightBound F reach p.2)
      (htie : ∀ q ∈ F, q.1 < reach → q.2 = p.2 → p.1 ≤ q.1)
      (tail : GreedyTail F s reach p.2 rest) :
      GreedyTail F s previous reach (p :: rest)

/-- Integer progress, not a supplied finite cutoff, yields a terminating tail. -/
theorem exists_greedy_tail (F : Finset Interval) (s previous reach : ℕ)
    (hvalid : Valid F s) (hcuts : Cuts F s)
    (hpositive : 0 < reach) (hbound : reach ≤ s)
    (hinvariant : RightBound F previous reach) :
    ∃ rest, GreedyTail F s previous reach rest := by
  classical
  have haux : ∀ n previous reach, s - reach = n → 0 < reach → reach ≤ s →
      RightBound F previous reach → ∃ rest, GreedyTail F s previous reach rest := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro previous reach hmeasure hpositive hbound hinvariant
      by_cases hend : reach = s
      · subst reach
        exact ⟨[], GreedyTail.done previous⟩
      have hless : reach < s := by omega
      obtain ⟨p, hp, hprevious, hleft, hadvance, hboundp, hmax, htie⟩ :=
        exists_greedy_step F s previous reach hvalid hcuts hpositive hless hinvariant
      have hdecrease : s - p.2 < n := by omega
      obtain ⟨rest, hrest⟩ := ih (s - p.2) hdecrease reach p.2 rfl
        (by omega) hboundp hmax
      exact ⟨p :: rest, GreedyTail.step previous reach p rest hp hprevious hleft
        hadvance hboundp hmax htie hrest⟩
  exact haux (s - reach) previous reach rfl hpositive hbound hinvariant

def endRight : ℕ → List Interval → ℕ
  | reach, [] => reach
  | _, p :: rest => endRight p.2 rest

theorem GreedyTail.end_eq {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    endRight reach rest = s := by
  induction h with
  | done previous => rfl
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    exact ih

theorem GreedyTail.mem {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    ∀ p ∈ rest, p ∈ F := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ih q hq

theorem GreedyTail.length_le {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    rest.length ≤ s - reach := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    simp only [List.length_cons]
    omega

theorem GreedyTail.strict_right {F : Finset Interval} {s previous reach : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest) :
    rest.Pairwise (fun p q => p.2 < q.2) ∧ ∀ q ∈ rest, reach < q.2 := by
  induction h with
  | done previous => exact ⟨List.Pairwise.nil, by simp⟩
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    rcases ih with ⟨ihpairwise, ihgreater⟩
    refine ⟨List.Pairwise.cons ihgreater ihpairwise, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hadvance
    · exact lt_trans hadvance (ihgreater q hq)

/-- The min-left tie is what bounds the final left end by the last boundary
interval; an arbitrary maximum-right choice would not justify this result. -/
theorem GreedyTail.terminal_left_le {F : Finset Interval} {s previous reach b : ℕ}
    {rest : List Interval} (h : GreedyTail F s previous reach rest)
    (hboundary : (b, s) ∈ F) :
    ∀ q ∈ rest, q.2 = s → q.1 ≤ b := by
  induction h with
  | done previous => simp
  | step previous reach p rest hp hprevious hleft hadvance hbound hmaximum htie tail ih =>
    intro q hq hqend
    rcases List.mem_cons.mp hq with rfl | hq
    · by_cases hb : b < reach
      · exact htie (b, s) hboundary hb hqend.symm
      · have hreach : reach ≤ b := by omega
        exact le_trans (Nat.le_of_lt hleft) hreach
    · exact ih q hq hqend

/-- Actual finite interval-family theorem with both boundary intervals.
The nonempty output list ends at s, has at most s members, and its returned
recursive certificate gives the stated greedy interleaving and membership.
Its first right end is at least a; every selected interval ending at s starts
at or before b. `2 ≤ s` excludes the vacuous empty-family s=1 counterexample. -/
theorem exists_interval_vine (F : Finset Interval) (s a b : ℕ)
    (hs : 2 ≤ s) (hvalid : Valid F s) (hcuts : Cuts F s)
    (hfirst : (0, a) ∈ F) (hlast : (b, s) ∈ F) :
    ∃ first rest, first ∈ F ∧ first.1 = 0 ∧ a ≤ first.2 ∧
      (∀ q ∈ F, q.1 = 0 → q.2 ≤ first.2) ∧
      GreedyTail F s 1 first.2 rest ∧
      (first :: rest).Pairwise (fun p q => p.2 < q.2) ∧
      endRight 0 (first :: rest) = s ∧ (first :: rest).length ≤ s ∧
      (∀ q ∈ first :: rest, q ∈ F) ∧
      (∀ q ∈ first :: rest, q.2 = s → q.1 ≤ b) := by
  classical
  let S := F.filter (fun p => p.1 = 0)
  have hS : S.Nonempty := ⟨(0, a), Finset.mem_filter.mpr ⟨hfirst, rfl⟩⟩
  obtain ⟨first, hfirstS, hmax, hmin⟩ := exists_right_max_left_min S hS
  have hfirstF : first ∈ F := (Finset.mem_filter.mp hfirstS).1
  have hzero : first.1 = 0 := (Finset.mem_filter.mp hfirstS).2
  have hfirstmax : ∀ q ∈ F, q.1 = 0 → q.2 ≤ first.2 := by
    intro q hq hqzero
    exact hmax q (Finset.mem_filter.mpr ⟨hq, hqzero⟩)
  have ha : a ≤ first.2 := hfirstmax (0, a) hfirst rfl
  obtain ⟨cross, hcross, hcrossL, hcrossR⟩ := hcuts 1 (by omega) (by omega)
  have hcrosszero : cross.1 = 0 := by omega
  have hreach : 1 < first.2 := lt_of_lt_of_le hcrossR (hfirstmax cross hcross hcrosszero)
  have hinvariant : RightBound F 1 first.2 := by
    intro q hq hqL
    exact hfirstmax q hq (by omega)
  obtain ⟨rest, hrest⟩ := exists_greedy_tail F s 1 first.2 hvalid hcuts
    (by omega) (hvalid first hfirstF).2 hinvariant
  refine ⟨first, rest, hfirstF, hzero, ha, hfirstmax, hrest,
    List.Pairwise.cons hrest.strict_right.2 hrest.strict_right.1, hrest.end_eq, ?_, ?_, ?_⟩
  · have hlength := hrest.length_le
    have hbound := (hvalid first hfirstF).2
    simp only [List.length_cons]
    omega
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hfirstF
    · exact hrest.mem q hq
  · intro q hq hqend
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hzero]
      exact Nat.zero_le b
    · exact hrest.terminal_left_le hlast q hq hqend

end ErdosProblems.PathUpperReduction.IntervalVine
