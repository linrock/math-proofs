module

public import LowDensityDegreeCleaning546
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[expose] public section

/-!
# Real density consequences of the exact degree-pruning budget

The graph degrees and all deleted cardinalities remain natural numbers.
Floors are used only to select the pruning threshold.
-/

namespace Erdos546

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem redDegreeSum_eq_card_interedges (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V) : redDegreeSum H S = (H.interedges S S).card := by
  simp only [SimpleGraph.interedges_def, redDegreeSum, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

omit [DecidableEq V] in
/-- Convert the library's diagonal edge density to the exact degree budget. -/
theorem redDegreeSum_le_of_edgeDensity_le
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (ε : ℝ)
    (hdensity : (H.edgeDensity S S : ℝ) ≤ ε) :
    (redDegreeSum H S : ℝ) ≤ ε * S.card ^ 2 := by
  by_cases hS : S.card = 0
  · have hSempty : S = ∅ := card_eq_zero.mp hS
    subst S
    simp [redDegreeSum]
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS
  rw [SimpleGraph.edgeDensity_def] at hdensity
  push_cast at hdensity
  rw [redDegreeSum_eq_card_interedges]
  simpa only [pow_two] using (div_le_iff₀ (mul_pos hSpos hSpos)).mp hdensity

/-- The first cleaning in Sudakov's low-density lemma, with exact natural
degrees and the original real threshold. -/
theorem exists_half_subset_degree_le_density
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (ε : ℝ)
    (hε : 0 < ε) (hmass : (redDegreeSum H S : ℝ) ≤ ε * S.card ^ 2) :
    ∃ T : Finset V, T ⊆ S ∧ S.card ≤ 2 * T.card ∧
      ∀ v ∈ T, ((T.filter (H.Adj v)).card : ℝ) ≤ ε * S.card := by
  by_cases hS : S.card = 0
  · have hSempty : S = ∅ := card_eq_zero.mp hS
    subst S
    exact ⟨∅, Subset.rfl, by simp, by simp⟩
  have hN : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hS)
  let d : ℕ := ⌊ε * S.card⌋₊ + 1
  have hd : ε * S.card < (d : ℝ) := by
    simpa only [d, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (ε * S.card)
  obtain ⟨T, hTS, hdeg, hcharge⟩ := exists_low_degree_subset H S d
  have hcard : T.card ≤ S.card := card_le_card hTS
  have hdiff : ((S.card - T.card : ℕ) : ℝ) = (S.card : ℝ) - T.card :=
    Nat.cast_sub hcard
  have hchargeR : 2 * (d : ℝ) * ((S.card : ℝ) - T.card) ≤ ε * S.card ^ 2 := by
    have hc : ((2 * d * (S.card - T.card) : ℕ) : ℝ) ≤ (redDegreeSum H S : ℝ) := by
      exact_mod_cast (show 2 * d * (S.card - T.card) ≤ redDegreeSum H S by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hdiff] using hc.trans hmass
  have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) - T.card :=
    sub_nonneg.mpr (Nat.cast_le.mpr hcard)
  have hmul := mul_le_mul_of_nonneg_right hd.le (show 0 ≤ 2 * ((S.card : ℝ) - T.card) by positivity)
  have hcancel : ε * S.card * (2 * ((S.card : ℝ) - T.card)) ≤ ε * S.card * S.card := by
    nlinarith
  have hdeleted : 2 * ((S.card : ℝ) - T.card) ≤ S.card :=
    (mul_le_mul_iff_of_pos_left (mul_pos hε hN)).mp hcancel
  refine ⟨T, hTS, ?_, ?_⟩
  · have : (S.card : ℝ) ≤ 2 * T.card := by linarith
    exact_mod_cast this
  · intro v hv
    have hfloor : (T.filter (H.Adj v)).card ≤ ⌊ε * S.card⌋₊ := by
      have := hdeg v hv
      dsimp [d] at this
      omega
    exact (Nat.cast_le.mpr hfloor).trans (Nat.floor_le (by positivity))

/-- Remove the vertices with too many red neighbors in a blue clique.
The deleted cardinality is at most one third of the original host size. -/
theorem exists_third_budget_mask_subset
    (H : SimpleGraph V) [DecidableRel H.Adj] (S B : Finset V) (N : ℕ) (ε : ℝ)
    (hε : 0 < ε) (hB : 0 < B.card)
    (hdeg : ∀ b ∈ B, ((S.filter (H.Adj b)).card : ℝ) ≤ ε * N) :
    ∃ F : Finset V, F ⊆ S \ B ∧
      ((S \ B).card : ℝ) ≤ F.card + (N : ℝ) / 3 ∧
      ∀ v ∈ F, ((B.filter (H.Adj v)).card : ℝ) ≤ 3 * ε * B.card := by
  classical
  let P := S \ B
  let w : V → ℝ := fun v => (B.filter (H.Adj v)).card
  let τ : ℝ := 3 * ε * B.card
  let F := P.filter (fun v => w v ≤ τ)
  let bad := P.filter (fun v => ¬ w v ≤ τ)
  have hpartition : F.card + bad.card = P.card := card_filter_add_card_filter_not _
  have hsum : (∑ v ∈ P, w v) ≤ ε * N * B.card := by
    have hswap : (∑ v ∈ P, (B.filter (H.Adj v)).card) =
        ∑ b ∈ B, (P.filter (H.Adj b)).card := by
      have hcard (C : Finset V) (p : V → Prop) [DecidablePred p] :
          (C.filter p).card = ∑ x ∈ C, if p x then (1 : ℕ) else 0 := by
        exact (Finset.sum_boole p C).symm
      simp_rw [hcard]
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro v hv
      simp only [H.adj_comm v b]
    rw [show (∑ v ∈ P, w v) = ∑ v ∈ P, ((B.filter (H.Adj v)).card : ℝ) by rfl]
    rw [← Nat.cast_sum, hswap, Nat.cast_sum]
    calc
      (∑ b ∈ B, ((P.filter (H.Adj b)).card : ℝ)) ≤ ∑ b ∈ B, ε * N := by
        apply sum_le_sum
        intro b hb
        exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ Finset.sdiff_subset))).trans
          (hdeg b hb)
      _ = ε * N * B.card := by simp [mul_comm]
  have hbadlower : τ * bad.card ≤ ∑ v ∈ bad, w v := by
    calc
      τ * bad.card = ∑ _v ∈ bad, τ := by simp [mul_comm]
      _ ≤ ∑ v ∈ bad, w v := sum_le_sum (by
        intro v hv
        exact (lt_of_not_ge (mem_filter.mp hv).2).le)
  have hbadupper : (∑ v ∈ bad, w v) ≤ ∑ v ∈ P, w v :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; dsimp [w]; positivity)
  have hbadmass : ε * B.card * (3 * bad.card) ≤ ε * B.card * N := by
    dsimp [τ] at hbadlower
    nlinarith [hbadlower.trans (hbadupper.trans hsum)]
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB
  have hbadcard : 3 * (bad.card : ℝ) ≤ N :=
    (mul_le_mul_iff_of_pos_left (mul_pos hε hBpos)).mp hbadmass
  refine ⟨F, filter_subset _ _, ?_, ?_⟩
  · have hpR : (F.card : ℝ) + bad.card = P.card := by exact_mod_cast hpartition
    dsimp only [P] at hpR
    linarith
  · intro v hv
    exact (mem_filter.mp hv).2

end Erdos546
