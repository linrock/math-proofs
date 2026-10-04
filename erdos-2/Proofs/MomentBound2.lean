module

public import Mathlib


@[expose] public section

/-!
# Weighted second-moment expansion over finite indicator families

Expands the weighted square $\sum_x w(x) (\sum_{i : x \in S_i} c_i)^2$ as the
double intersection sum $\sum_{i, j} c_i c_j \sum_{x \in S_i \cap S_j} w(x)$.
-/

namespace Erdos2.Moments

open scoped BigOperators

theorem weighted_indicator_square {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq Ω] (w : Ω → ℝ) (c : I → ℝ) (S : I → Finset Ω) :
    (∑ x, w x * (∑ i, if x ∈ S i then c i else 0) ^ 2) =
      ∑ i, ∑ j, c i * c j * ∑ x ∈ S i ∩ S j, w x := by
  classical
  calc
    _ = ∑ x, ∑ i, ∑ j,
        (c i * c j) * (if x ∈ S i ∩ S j then w x else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Fintype.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hxi : x ∈ S i <;> by_cases hxj : x ∈ S j <;>
        (simp [hxi, hxj]; try ring)
    _ = ∑ i, ∑ j, c i * c j * ∑ x ∈ S i ∩ S j, w x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp

/-- Any nonnegative pointwise indicator majorant yields a second-moment bound
from weighted pair-intersection estimates. Diagonal pairs are included. -/
theorem second_moment_le_pair_intersections {Ω I : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq Ω] (w : Ω → ℝ) (c : I → ℝ)
    (S : I → Finset Ω) (α : Ω → ℝ) (H : I → I → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hc : ∀ i, 0 ≤ c i)
    (hα_nonneg : ∀ x, 0 ≤ α x)
    (hα_le : ∀ x, α x ≤ ∑ i, if x ∈ S i then c i else 0)
    (hH : ∀ i j, (∑ x ∈ S i ∩ S j, w x) ≤ H i j) :
    (∑ x, w x * (α x) ^ 2) ≤ ∑ i, ∑ j, c i * c j * H i j := by
  classical
  calc
    _ ≤ ∑ x, w x * (∑ i, if x ∈ S i then c i else 0) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (hw x)
      exact (sq_le_sq₀ (hα_nonneg x) ((hα_nonneg x).trans (hα_le x))).2 (hα_le x)
    _ = ∑ i, ∑ j, c i * c j * ∑ x ∈ S i ∩ S j, w x :=
      weighted_indicator_square w c S
    _ ≤ ∑ i, ∑ j, c i * c j * H i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hH i j) (mul_nonneg (hc i) (hc j))

end Erdos2.Moments
