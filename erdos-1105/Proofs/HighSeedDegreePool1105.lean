module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic

@[expose] public section

/-!
# An original-degree pool in a dense terminal seed

All degrees and the edge count refer to the SAME supplied graph.

The nontruncated twice-edge hypothesis is
`d * (d - 1) + 2 * d * h ≤ 2 * |E(G)| + 2 * (h - 3)`. For `h ≥ 3`, this expresses deficit at most `h - 3` from the d-degenerate
edge ceiling at order `d + h`, without introducing natural-number division.
-/

namespace ErdosProblems.AntiRamseyHighSeedDegreePool1105

open scoped BigOperators

/-- At least `d - 1` vertices have original degree at least `d + 1`.
No minimum-degree assumption is needed for this counting statement. -/
theorem high_seed_degree_pool {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d h : ℕ}
    (hd : 4 ≤ d) (hh : 3 ≤ h)
    (horder : Fintype.card V = d + h)
    (hedges : d * (d - 1) + 2 * d * h ≤
      2 * G.edgeFinset.card + 2 * (h - 3)) :
    d - 1 ≤ (Finset.univ.filter fun v : V => d + 1 ≤ G.degree v).card := by
  classical
  let S : Finset V := Finset.univ.filter fun v => d + 1 ≤ G.degree v
  by_contra hpool
  change ¬ d - 1 ≤ S.card at hpool
  have hsmall : S.card ≤ d - 2 := by omega
  have hdegree (v : V) :
      G.degree v ≤ d + (if v ∈ S then h - 1 else 0) := by
    split_ifs with hv
    · have hvmax := G.degree_lt_card_verts v
      rw [horder] at hvmax
      omega
    · have hvlow : ¬ d + 1 ≤ G.degree v := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hv
      omega
  have hpiece :
      (∑ v : V, if v ∈ S then h - 1 else 0) = S.card * (h - 1) := by
    calc
      _ = (∑ v : V, if v ∈ S then 1 else 0) * (h - 1) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ = S.card * (h - 1) := by
        rw [← Finset.card_eq_sum_ite (Finset.subset_univ S)]
  have hsum : (∑ v : V, G.degree v) ≤
      (d + h) * d + S.card * (h - 1) := by
    calc
      _ ≤ ∑ v : V, (d + (if v ∈ S then h - 1 else 0)) := by
        apply Finset.sum_le_sum
        intro v _
        exact hdegree v
      _ = (d + h) * d + S.card * (h - 1) := by
        rw [Finset.sum_add_distrib, hpiece, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, horder]
        simp only [Nat.cast_id]
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hupper : 2 * G.edgeFinset.card ≤
      (d + h) * d + (d - 2) * (h - 1) :=
    hsum.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (h - 1) hsmall) _)
  have hupperZ : (2 : ℤ) * (G.edgeFinset.card : ℤ) ≤
      ((d + h : ℕ) : ℤ) * (d : ℤ) +
        ((d - 2 : ℕ) : ℤ) * ((h - 1 : ℕ) : ℤ) := by
    exact_mod_cast hupper
  have hedgesZ : (d : ℤ) * ((d - 1 : ℕ) : ℤ) +
      2 * (d : ℤ) * (h : ℤ) ≤
        2 * (G.edgeFinset.card : ℤ) + 2 * ((h - 3 : ℕ) : ℤ) := by
    exact_mod_cast hedges
  simp only [Nat.cast_add,
    Nat.cast_sub (show 2 ≤ d by omega),
    Nat.cast_sub (show 1 ≤ d by omega),
    Nat.cast_sub (show 1 ≤ h by omega),
    Nat.cast_sub hh, Nat.cast_ofNat, Nat.cast_one] at hupperZ hedgesZ
  nlinarith

end ErdosProblems.AntiRamseyHighSeedDegreePool1105

