module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic


@[expose] public section

/-!
# Degree pruning for Sudakov's small-density Ramsey lemma

`redDegreeSum` counts ordered red edges inside a finite vertex set. Removing
a vertex of red degree at least `d` charges at least `2*d` from this sum.
The resulting induced graph has red maximum degree less than `d`.
-/

namespace Erdos546

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

def redDegreeSum (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℕ :=
  ∑ v ∈ S, (S.filter (H.Adj v)).card

theorem neighbor_card_erase_add (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) (w : V) :
    ((S.erase v).filter (H.Adj w)).card + (if H.Adj w v then 1 else 0) =
      (S.filter (H.Adj w)).card := by
  rw [filter_erase]
  split_ifs with h
  · rw [card_erase_of_mem (mem_filter.mpr ⟨hv, h⟩)]
    have : 0 < (S.filter (H.Adj w)).card := card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, h⟩⟩
    omega
  · rw [erase_eq_of_notMem]
    · omega
    · simp [h]

theorem redDegreeSum_erase (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    redDegreeSum H (S.erase v) + 2 * (S.filter (H.Adj v)).card =
      redDegreeSum H S := by
  have hsum : (∑ w ∈ S.erase v, (S.filter (H.Adj w)).card) =
      redDegreeSum H (S.erase v) + (S.filter (H.Adj v)).card := by
    calc
      (∑ w ∈ S.erase v, (S.filter (H.Adj w)).card) =
          ∑ w ∈ S.erase v,
            (((S.erase v).filter (H.Adj w)).card + if H.Adj w v then 1 else 0) := by
        apply sum_congr rfl
        intro w hw
        exact (neighbor_card_erase_add H S hv w).symm
      _ = redDegreeSum H (S.erase v) +
          ∑ w ∈ S.erase v, if H.Adj w v then 1 else 0 := by
        rw [sum_add_distrib]
        rfl
      _ = redDegreeSum H (S.erase v) + (S.filter (H.Adj v)).card := by
        rw [sum_boole]
        congr 1
        apply congrArg Finset.card
        ext w
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨⟨hwn, hwS⟩, hred⟩
          exact ⟨hwS, hred.symm⟩
        · rintro ⟨hwS, hred⟩
          exact ⟨⟨hred.ne.symm, hwS⟩, hred.symm⟩
  calc
    redDegreeSum H (S.erase v) + 2 * (S.filter (H.Adj v)).card =
        (∑ w ∈ S.erase v, (S.filter (H.Adj w)).card) +
          (S.filter (H.Adj v)).card := by rw [hsum]; omega
    _ = redDegreeSum H S := sum_erase_add S (fun w => (S.filter (H.Adj w)).card) hv

/-- Exact degree-pruning budget. The deleted vertices charge distinct edge
incidences; no independent density or probability assumption is used. -/
theorem exists_low_degree_subset (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (d : ℕ) :
    ∃ T : Finset V, T ⊆ S ∧
      (∀ v ∈ T, (T.filter (H.Adj v)).card < d) ∧
      2 * d * (S.card - T.card) + redDegreeSum H T ≤ redDegreeSum H S := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hsmall : ∀ v ∈ S, (S.filter (H.Adj v)).card < d
    · exact ⟨S, Subset.rfl, hsmall, by simp⟩
    · push Not at hsmall
      obtain ⟨v, hv, hlarge⟩ := hsmall
      obtain ⟨T, hT, hdeg, hbudget⟩ := ih (S.erase v) (erase_ssubset hv)
      refine ⟨T, hT.trans (erase_subset _ _), hdeg, ?_⟩
      have hcard : T.card ≤ (S.erase v).card := card_le_card hT
      have hSpos : 0 < S.card := card_pos.mpr ⟨v, hv⟩
      have herase : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
      have hmass := redDegreeSum_erase H S hv
      have hdiff : S.card - T.card = (S.erase v).card - T.card + 1 := by omega
      rw [hdiff, Nat.mul_add, Nat.mul_one]
      have hcharge : 2 * d ≤ 2 * (S.filter (H.Adj v)).card := Nat.mul_le_mul_left 2 hlarge
      omega

/-- If the degree sum fits a deletion budget, enough vertices survive. -/
theorem exists_low_degree_subset_of_budget (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) (d b : ℕ) (hd : 0 < d)
    (hbudget : redDegreeSum H S ≤ 2 * d * b) :
    ∃ T : Finset V, T ⊆ S ∧ S.card - b ≤ T.card ∧
      ∀ v ∈ T, (T.filter (H.Adj v)).card < d := by
  obtain ⟨T, hTS, hdeg, hcharge⟩ := exists_low_degree_subset H S d
  refine ⟨T, hTS, ?_, hdeg⟩
  have hprod : 2 * d * (S.card - T.card) ≤ 2 * d * b := by omega
  have hdeleted : S.card - T.card ≤ b := by nlinarith
  omega

#print axioms neighbor_card_erase_add
#print axioms redDegreeSum_erase
#print axioms exists_low_degree_subset
#print axioms exists_low_degree_subset_of_budget

end Erdos546
