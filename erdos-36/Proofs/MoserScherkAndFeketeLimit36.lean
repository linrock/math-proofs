module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import MinimumOverlapFoundations36
@[expose] public section
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
noncomputable section
open scoped Topology BigOperators
open Filter
namespace Erdos36.Proofs

/-- Non-negativity of the minimum overlap quotient `MinOverlapQuotient n = M n / n` for all $n \in \mathbb{N}$. -/
theorem minOverlapQuotient_nonneg (n : ℕ) : 0 ≤ MinOverlapQuotient n := by
  unfold MinOverlapQuotient
  positivity

/-- `MinOverlapQuotient` is bounded above along `atTop` (by $1$). -/
theorem isBoundedUnder_le_minOverlapQuotient :
    Filter.IsBoundedUnder (· ≤ ·) atTop MinOverlapQuotient :=
  Filter.isBoundedUnder_of ⟨1, minOverlapQuotient_le_one⟩

/-- `MinOverlapQuotient` is bounded below along `atTop` (by $0$). -/
theorem isBoundedUnder_ge_minOverlapQuotient :
    Filter.IsBoundedUnder (· ≥ ·) atTop MinOverlapQuotient :=
  Filter.isBoundedUnder_of ⟨0, minOverlapQuotient_nonneg⟩

/-- **Fekete Limsup-Liminf Inequality**: since `atTop.limsup MinOverlapQuotient ≤ MinOverlapQuotient k`
holds for every $k \ge 1$ (`fekete_limsup_minOverlapQuotient_le_div`), taking `liminf` over $k$ yields
`atTop.limsup MinOverlapQuotient ≤ atTop.liminf MinOverlapQuotient`. -/
theorem limsup_le_liminf_minOverlapQuotient :
    atTop.limsup MinOverlapQuotient ≤ atTop.liminf MinOverlapQuotient := by
  apply Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le atTop minOverlapQuotient_le_one)
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact fekete_limsup_minOverlapQuotient_le_div hk

/-- Standard order inequality `atTop.liminf MinOverlapQuotient ≤ atTop.limsup MinOverlapQuotient`
from boundedness of `MinOverlapQuotient` in $[0, 1]$. -/
theorem liminf_le_limsup_minOverlapQuotient :
    atTop.liminf MinOverlapQuotient ≤ atTop.limsup MinOverlapQuotient :=
  Filter.liminf_le_limsup isBoundedUnder_le_minOverlapQuotient isBoundedUnder_ge_minOverlapQuotient

/-- **Fekete Limit Equality for the Minimum Overlap Quotient**:
`atTop.liminf MinOverlapQuotient = atTop.limsup MinOverlapQuotient`. -/
theorem liminf_eq_limsup_minOverlapQuotient :
    atTop.liminf MinOverlapQuotient = atTop.limsup MinOverlapQuotient :=
  le_antisymm liminf_le_limsup_minOverlapQuotient limsup_le_liminf_minOverlapQuotient

/-- **Unconditional Existence of the Minimum Overlap Limit (Liminf Form)**:
`MinOverlapQuotient` converges along `atTop` to `atTop.liminf MinOverlapQuotient`. -/
theorem tendsto_minOverlapQuotient_liminf :
    atTop.Tendsto MinOverlapQuotient (𝓝 (atTop.liminf MinOverlapQuotient)) :=
  tendsto_of_liminf_eq_limsup rfl liminf_eq_limsup_minOverlapQuotient.symm
    isBoundedUnder_le_minOverlapQuotient isBoundedUnder_ge_minOverlapQuotient

/-- Closed-form sum of squares on `Finset.range N`:
`6 * ∑ k ∈ range N, (k + 1)^2 = N * (N + 1) * (2N + 1)`. -/
theorem six_mul_sum_range_sq_eq : ∀ N : ℕ,
    6 * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2) =
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, mul_add, six_mul_sum_range_sq_eq N]
    push_cast
    ring

/-- Folding the symmetric second moment $\sum_{k=-N}^N k^2 \operatorname{Overlap}(A,B,k)$
onto positive shifts $k \in \operatorname{range} N$ for any disjoint sets $A, B$. -/
theorem sum_Icc_symm_sq_overlap_eq_sum_range {A B : Finset ℤ}
    (hdisj : Disjoint A B) : ∀ N : ℕ,
    ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (k : ℝ) ^ 2 * (Overlap A B k : ℝ) =
      ∑ k ∈ Finset.range N,
        ((k + 1 : ℕ) : ℝ) ^ 2 *
          ((Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ))) : ℕ) : ℝ)
  | 0 => by simp [overlap_zero_eq_zero_of_disjoint hdisj]
  | N + 1 => by
    have hsplit : Finset.Icc (-(((N + 1 : ℕ) : ℤ))) ((N + 1 : ℕ) : ℤ) =
        insert (((N + 1 : ℕ) : ℤ))
          (insert (-(((N + 1 : ℕ) : ℤ))) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hm1 : (((N + 1 : ℕ) : ℤ)) ∉
        insert (-(((N + 1 : ℕ) : ℤ))) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hm2 : (-(((N + 1 : ℕ) : ℤ))) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hm1, Finset.sum_insert hm2,
      sum_Icc_symm_sq_overlap_eq_sum_range hdisj N, Finset.sum_range_succ]
    push_cast
    ring

/-- Folding the second moment of `Overlap A B` on `[-(2n-1), 2n-1]` into the positive-shift
pair-overlap sum over `Finset.range (2 * n)`. -/
theorem sum_range_sq_overlap_add_neg_eq {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n)) (hB : B ⊆ Finset.Icc (1 : ℤ) (2 * n)) :
    ∑ k ∈ Finset.range (2 * n),
      ((k + 1 : ℕ) : ℝ) ^ 2 *
        ((Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ))) : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
        (k : ℝ) ^ 2 * (Overlap A B k : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hemp : Finset.Icc (-((2 : ℤ) * (0 : ℕ) - 1)) ((2 : ℤ) * (0 : ℕ) - 1) = ∅ := by decide
    simp [hemp]
  · have hN : (2 : ℤ) * (n : ℤ) - 1 = ((2 * n - 1 : ℕ) : ℤ) := by omega
    rw [hN, sum_Icc_symm_sq_overlap_eq_sum_range hdisj (2 * n - 1)]
    have hsucc : 2 * n = (2 * n - 1) + 1 := by omega
    conv_lhs => rw [hsucc, Finset.sum_range_succ]
    have hle := overlap_add_overlap_neg_le_sub hdisj hA hB (k := 2 * n - 1 + 1)
    have hzero : Overlap A B (((2 * n - 1 + 1 : ℕ) : ℤ)) +
        Overlap A B (-(((2 * n - 1 + 1 : ℕ) : ℤ))) = 0 := by omega
    rw [hzero]
    simp

/-- Closed-form sum of the positive-shift parabolic kernel on `Finset.range R`:
`6 * ∑ k ∈ range R, (R^2 - (k + 1)^2) = R * (4 * R^2 - 3 * R - 1)`. -/
theorem six_mul_sum_range_parabolic_kernel_eq (R : ℕ) :
    6 * (∑ k ∈ Finset.range R, ((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2)) =
      (R : ℝ) * (4 * (R : ℝ) ^ 2 - 3 * (R : ℝ) - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub]
  have h6 := six_mul_sum_range_sq_eq R
  linarith

/-- **Unshifted Scherk-Capped Parabolic Bathtub Inequality**: for any balanced partition $(A, B)$
of `[1, 2n]` with $m = \operatorname{MaxOverlap}(A, B)$ and any radius $R \in \mathbb{N}$,
combining the zero-overlap exclusion $\operatorname{Overlap}(A, B, 0) = 0$ and Scherk's symmetric
pair bound $\operatorname{Overlap}(A, B, k) + \operatorname{Overlap}(A, B, -k) \le \min(2m, 2n - k)$
with Moser's unshifted second-moment identity yields:
`6 R^2 n^2 - n^2(4n^2 - 1) - 3 Δ^2 + 6 R^2 m + 6 ∑_{k < R} (R^2 - (k+1)^2)(2m - (2n - 1 - k)) ≤ 2 R (4R^2 - 1) m`. -/
theorem unshifted_scherk_parabolic_bathtub_inequality {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (R : ℕ) :
    6 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 - (n : ℝ) ^ 2 * (4 * (n : ℝ) ^ 2 - 1) -
      3 * (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ)) ^ 2 +
      6 * (R : ℝ) ^ 2 * (MaxOverlap A B : ℝ) +
      6 * (∑ k ∈ Finset.range R,
        (((R ^ 2 - (k + 1) ^ 2) * (2 * MaxOverlap A B - (2 * n - 1 - k)) : ℕ) : ℝ)) ≤
      2 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
  have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
  have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
  set m := MaxOverlap A B
  set P : ℕ → ℕ := fun k =>
    Overlap A B (((k + 1 : ℕ) : ℤ)) + Overlap A B (-(((k + 1 : ℕ) : ℤ)))
  have hm0 : ∑ k ∈ Finset.range (2 * n), (P k : ℝ) = (n : ℝ) ^ 2 := by
    have h0 := sum_range_overlap_add_neg_eq_card_mul hdisj hA_sub hB_sub
    rw [hA, hB, ← sq] at h0
    exact_mod_cast h0
  have hm2 : 6 * (∑ k ∈ Finset.range (2 * n), ((k + 1 : ℕ) : ℝ) ^ 2 * (P k : ℝ)) =
      (n : ℝ) ^ 2 * (4 * (n : ℝ) ^ 2 - 1) +
        3 * (∑ a ∈ A, (a : ℝ) - ∑ b ∈ B, (b : ℝ)) ^ 2 := by
    rw [sum_range_sq_overlap_add_neg_eq hdisj hA_sub hB_sub]
    exact moser_second_moment_variance_identity hdisj hunion hA hB
  have hdiff : (R : ℝ) ^ 2 * (n : ℝ) ^ 2 -
      ∑ k ∈ Finset.range (2 * n), ((k + 1 : ℕ) : ℝ) ^ 2 * (P k : ℝ) =
      ∑ k ∈ Finset.range (2 * n), (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * (P k : ℝ)) := by
    rw [← hm0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hstep1 : ∑ k ∈ Finset.range (2 * n), (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * (P k : ℝ)) ≤
      ∑ k ∈ Finset.range (2 * n),
        if k ∈ Finset.range R then
          (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * ((min (2 * m) (2 * n - 1 - k) : ℕ) : ℝ))
        else 0 := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2n : k < 2 * n := Finset.mem_range.mp hk
    split_ifs with hkR
    · have hk_lt : k < R := Finset.mem_range.mp hkR
      have hsq : (k + 1) ^ 2 ≤ R ^ 2 := by nlinarith
      have hsq_real : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq
      have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2 := by linarith
      have hcap := overlap_add_overlap_neg_le_min hdisj hA_sub hB_sub (k := k + 1) (by omega)
      have hsub : 2 * n - (k + 1) = 2 * n - 1 - k := by omega
      rw [hsub] at hcap
      have hcap_real : (P k : ℝ) ≤ ((min (2 * m) (2 * n - 1 - k) : ℕ) : ℝ) := by
        exact_mod_cast hcap
      exact mul_le_mul_of_nonneg_left hcap_real hnonneg
    · have hk_ge : R ≤ k := le_of_not_gt (Finset.mem_range.not.mp hkR)
      have hsq : R ^ 2 ≤ (k + 1) ^ 2 := by nlinarith
      have hsq_real : (R : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hsq
      have hnonpos : (R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg hnonpos (by positivity)
  have hstep2 : (∑ k ∈ Finset.range (2 * n),
        if k ∈ Finset.range R then
          (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * ((min (2 * m) (2 * n - 1 - k) : ℕ) : ℝ))
        else 0) ≤
      ∑ k ∈ Finset.range R,
        (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * ((min (2 * m) (2 * n - 1 - k) : ℕ) : ℝ)) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => (Finset.mem_filter.mp hk).2) (fun k hk _ => ?_)
    have hk_lt : k < R := Finset.mem_range.mp hk
    have hsq : (k + 1) ^ 2 ≤ R ^ 2 := by nlinarith
    have hsq_real : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq
    have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2 := by linarith
    exact mul_nonneg hnonneg (by positivity)
  have hdecomp : ∀ k ∈ Finset.range R,
      (((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * ((min (2 * m) (2 * n - 1 - k) : ℕ) : ℝ)) +
        (((R ^ 2 - (k + 1) ^ 2) * (2 * m - (2 * n - 1 - k)) : ℕ) : ℝ) =
      ((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * (2 * (m : ℝ)) := by
    intro k hk
    have hk_lt : k < R := Finset.mem_range.mp hk
    have hsq : (k + 1) ^ 2 ≤ R ^ 2 := by nlinarith
    have hmin_add : min (2 * m) (2 * n - 1 - k) + (2 * m - (2 * n - 1 - k)) = 2 * m := by omega
    have hcast_mul : (((R ^ 2 - (k + 1) ^ 2) * (2 * m - (2 * n - 1 - k)) : ℕ) : ℝ) =
        ((R : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) * ((2 * m - (2 * n - 1 - k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hsq]
      push_cast
      rfl
    rw [hcast_mul, ← mul_add, ← Nat.cast_add, hmin_add]
    push_cast
    ring
  have hsum_decomp := Finset.sum_congr rfl hdecomp
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum_decomp
  have hpar := six_mul_sum_range_parabolic_kernel_eq R
  nlinarith

/-- **Universal Combined Moser-Scherk Cap-and-Moment Bound on `MaxOverlap`**:
for any balanced partition $(A, B)$ of `[1, 2n]` and any radius $R \in \mathbb{N}$,
averaging the unshifted Scherk-capped parabolic bathtub inequality (which has $-3\Delta^2$)
with the shifted Moser parabolic bathtub inequality (which has $+3\Delta^2$) cancels $\Delta^2$
identically and yields:
`12 R^2 n^2 + 6 R^2 MaxOverlap A B + 6 ∑_{k < R} (R^2 - (k+1)^2)(2 MaxOverlap A B - (2n - 1 - k)) ≤ 8 n^4 + 4 R (4 R^2 - 1) MaxOverlap A B`. -/
theorem moser_scherk_combined_le_maxOverlap {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (R : ℕ) :
    12 * R ^ 2 * n ^ 2 + 6 * R ^ 2 * MaxOverlap A B +
      6 * (∑ k ∈ Finset.range R,
        (R ^ 2 - (k + 1) ^ 2) * (2 * MaxOverlap A B - (2 * n - 1 - k))) ≤
      8 * n ^ 4 + 4 * R * (4 * R ^ 2 - 1) * MaxOverlap A B := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hA
    subst hA0
    have hm0 : MaxOverlap ∅ B = 0 := by
      exact Nat.eq_zero_of_le_zero ((maxOverlap_le_card_left ∅ B).trans (by simp))
    simp [hm0]
  · rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
      have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
      set Δℤ : ℤ := (∑ a ∈ A, a) - (∑ b ∈ B, b)
      obtain ⟨q₀, hq₀⟩ := exists_int_nearest_mul_le hn Δℤ
      have hq₀_real : 4 * ((n : ℝ) * (q₀ : ℝ) - ((∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ)))) ^ 2 ≤
          (n : ℝ) ^ 2 := by
        have hcast : ((n : ℤ) * q₀ - Δℤ : ℝ) =
            (n : ℝ) * (q₀ : ℝ) - ((∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ))) := by
          dsimp [Δℤ]; push_cast; ring
        have hq_cast : (4 * ((n : ℤ) * q₀ - Δℤ) ^ 2 : ℝ) ≤ ((n : ℤ) ^ 2 : ℝ) := by
          exact_mod_cast hq₀
        push_cast at hq_cast
        rw [← hcast]
        exact hq_cast
      have hunshift := unshifted_scherk_parabolic_bathtub_inequality hdisj hunion hA hB R
      have hshift := moser_shifted_second_moment_identity hdisj hunion hA hB (q₀ : ℝ)
      have hbat := parabolic_bathtub_overlap_inequality hA_sub hB_sub hA hB q₀ R
      have hreal : 12 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          6 * (R : ℝ) ^ 2 * (MaxOverlap A B : ℝ) +
          6 * (∑ k ∈ Finset.range R,
            (((R ^ 2 - (k + 1) ^ 2) * (2 * MaxOverlap A B - (2 * n - 1 - k)) : ℕ) : ℝ)) ≤
          8 * (n : ℝ) ^ 4 + 4 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
        linarith [sq_nonneg (n : ℝ)]
      have h4R2 : 1 ≤ 4 * R ^ 2 := by nlinarith
      have hcast_lhs : ((12 * R ^ 2 * n ^ 2 + 6 * R ^ 2 * MaxOverlap A B +
          6 * (∑ k ∈ Finset.range R,
            (R ^ 2 - (k + 1) ^ 2) * (2 * MaxOverlap A B - (2 * n - 1 - k))) : ℕ) : ℝ) =
          12 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          6 * (R : ℝ) ^ 2 * (MaxOverlap A B : ℝ) +
          6 * (∑ k ∈ Finset.range R,
            (((R ^ 2 - (k + 1) ^ 2) * (2 * MaxOverlap A B - (2 * n - 1 - k)) : ℕ) : ℝ)) := by
        push_cast
        ring
      have hcast_rhs : ((8 * n ^ 4 + 4 * R * (4 * R ^ 2 - 1) * MaxOverlap A B : ℕ) : ℝ) =
          8 * (n : ℝ) ^ 4 + 4 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
        push_cast [Nat.cast_sub h4R2]
        ring
      rw [← hcast_lhs, ← hcast_rhs] at hreal
      exact_mod_cast hreal

/-- **Universal Combined Moser-Scherk Cap-and-Moment Bound on $M(n)$**:
for all $n, R \in \mathbb{N}$,
`12 R^2 n^2 + 6 R^2 M n + 6 ∑_{k < R} (R^2 - (k+1)^2)(2 M n - (2n - 1 - k)) ≤ 8 n^4 + 4 R (4 R^2 - 1) M n`. -/
theorem moser_scherk_combined_le_M (n R : ℕ) :
    12 * R ^ 2 * n ^ 2 + 6 * R ^ 2 * M n +
      6 * (∑ k ∈ Finset.range R,
        (R ^ 2 - (k + 1) ^ 2) * (2 * M n - (2 * n - 1 - k))) ≤
      8 * n ^ 4 + 4 * R * (4 * R ^ 2 - 1) * M n := by
  have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
      (_disjoint : Disjoint A B)
      (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
      (_same_card : A.card = B.card)}).Nonempty := by
    refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
      Finset.disjoint_sdiff, ?_, ?_, rfl⟩
    · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
        Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
  have hcard_sum : A.card + B.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
    omega
  have hA : A.card = n := by omega
  have hB : B.card = n := by omega
  unfold M
  rw [← hM]
  exact moser_scherk_combined_le_maxOverlap hdisj hunion hA hB R

/-- **Punctured Downward-Parabolic Bathtub Inequality**: for any disjoint $A, B \subseteq [1, 2n]$
with $|A| = |B| = n$, any integer center $q_0 \in \mathbb{Z}$, and any radius $R \in \mathbb{N}$,
since $\operatorname{Overlap}(A, B, 0) = 0$, excluding $k = 0$ from $[q_0 - R, q_0 + R]$ strengthens
`parabolic_bathtub_overlap_inequality` by $+ 3 \max(0, R^2 - q_0^2) \operatorname{MaxOverlap}(A, B)$:
`3 R^2 n^2 - 3 ∑_k (k - q₀)^2 Overlap A B k + 3 max 0 (R^2 - q₀^2) MaxOverlap A B ≤ R (4 R^2 - 1) MaxOverlap A B`. -/
theorem punctured_parabolic_bathtub_overlap_inequality {n : ℕ} {A B : Finset ℤ}
    (hdisj : Disjoint A B)
    (hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n))
    (hA : A.card = n) (hB : B.card = n) (q₀ : ℤ) (R : ℕ) :
    3 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 -
      3 * (∑ k ∈ Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1),
        ((k : ℝ) - (q₀ : ℝ)) ^ 2 * (Overlap A B k : ℝ)) +
      3 * max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) * (MaxOverlap A B : ℝ) ≤
      (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (MaxOverlap A B : ℝ) := by
  set J := Finset.Icc (-((2 : ℤ) * n - 1)) ((2 : ℤ) * n - 1)
  set IR := Finset.Icc (q₀ - (R : ℤ)) (q₀ + (R : ℤ))
  set IR0 := IR.erase 0
  have hm0 : ∑ k ∈ J, (Overlap A B k : ℝ) = (n : ℝ) ^ 2 := by
    have h0 := sum_overlap_Icc_eq_card_mul hA_sub hB_sub
    rw [hA, hB] at h0
    have hcast : (∑ k ∈ J, Overlap A B k : ℝ) = ((n * n : ℕ) : ℝ) := by exact_mod_cast h0
    simpa [J, sq] using hcast
  have hdiff : (R : ℝ) ^ 2 * (n : ℝ) ^ 2 -
      ∑ k ∈ J, ((k : ℝ) - (q₀ : ℝ)) ^ 2 * (Overlap A B k : ℝ) =
      ∑ k ∈ J, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (Overlap A B k : ℝ) := by
    rw [← hm0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hstep1 : ∑ k ∈ J, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (Overlap A B k : ℝ) ≤
      ∑ k ∈ J,
        if k ∈ IR0 then ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) else 0 := by
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with hk
    · have hkI := Finset.mem_Icc.mp (Finset.mem_erase.mp hk).2
      have hsq_le : (k - q₀) ^ 2 ≤ (R : ℤ) ^ 2 := by nlinarith
      have hsq_real : ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq_le
      have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by linarith
      have hov : (Overlap A B k : ℝ) ≤ (MaxOverlap A B : ℝ) := by
        exact_mod_cast overlap_le_maxOverlap A B k
      exact mul_le_mul_of_nonneg_left hov hnonneg
    · by_cases hk0 : k = 0
      · subst hk0
        simp [overlap_zero_eq_zero_of_disjoint hdisj]
      · have hk_not_IR : k ∉ IR := fun h => hk (Finset.mem_erase.mpr ⟨hk0, h⟩)
        have hkI : k < q₀ - (R : ℤ) ∨ q₀ + (R : ℤ) < k := by
          rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk_not_IR
          exact hk_not_IR
        have hsq_ge : (R : ℤ) ^ 2 ≤ (k - q₀) ^ 2 := by
          rcases hkI with hlt | hgt <;> nlinarith
        have hsq_real : (R : ℝ) ^ 2 ≤ ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by exact_mod_cast hsq_ge
        have hnonpos : (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ 0 := by linarith
        exact mul_nonpos_of_nonpos_of_nonneg hnonpos (by positivity)
  have hstep2 : (∑ k ∈ J,
        if k ∈ IR0 then ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) else 0) ≤
      ∑ k ∈ IR0, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) * (MaxOverlap A B : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => (Finset.mem_filter.mp hk).2) (fun k hk _ => ?_)
    have hkI := Finset.mem_Icc.mp (Finset.mem_erase.mp hk).2
    have hsq_le : (k - q₀) ^ 2 ≤ (R : ℤ) ^ 2 := by nlinarith
    have hsq_real : ((k : ℝ) - (q₀ : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq_le
    have hnonneg : 0 ≤ (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2 := by linarith
    exact mul_nonneg hnonneg (by positivity)
  rw [← Finset.sum_mul] at hstep2
  have herase : (∑ k ∈ IR0, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2)) +
      max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) =
      ∑ k ∈ IR, ((R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) := by
    by_cases h0 : (0 : ℤ) ∈ IR
    · have h0I := Finset.mem_Icc.mp h0
      have hsq_le : q₀ ^ 2 ≤ (R : ℤ) ^ 2 := by nlinarith
      have hsq_real : (q₀ : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by exact_mod_cast hsq_le
      have hmax : max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) =
          (R : ℝ) ^ 2 - (((0 : ℤ) : ℝ) - (q₀ : ℝ)) ^ 2 := by
        rw [max_eq_right (by linarith)]
        ring
      rw [hmax]
      exact Finset.sum_erase_add IR (fun k => (R : ℝ) ^ 2 - ((k : ℝ) - (q₀ : ℝ)) ^ 2) h0
    · have h0I : (0 : ℤ) < q₀ - (R : ℤ) ∨ q₀ + (R : ℤ) < 0 := by
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at h0
        exact h0
      have hsq_ge : (R : ℤ) ^ 2 ≤ q₀ ^ 2 := by
        rcases h0I with hlt | hgt <;> nlinarith
      have hsq_real : (R : ℝ) ^ 2 ≤ (q₀ : ℝ) ^ 2 := by exact_mod_cast hsq_ge
      have hmax : max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) = 0 := max_eq_left (by linarith)
      have heq : IR0 = IR := Finset.erase_eq_of_notMem h0
      rw [hmax, heq, add_zero]
  have hpar := three_mul_sum_Icc_parabolic_kernel_eq q₀ R
  dsimp [J, IR, IR0] at hdiff hstep1 hstep2 herase ⊢
  nlinarith

/-- Quadratic dominance `4 * M n ≤ n ^ 2` for all $n \ge 2$ (whereas at $n = 1$, $4 M(1) = 4 > 1$). -/
theorem four_mul_M_le_sq {n : ℕ} (hn : 2 ≤ n) : 4 * M n ≤ n ^ 2 := by
  rcases eq_or_lt_of_le hn with rfl | hgt
  · rw [M_two_eq]; omega
  · have hle := M_le_add_one_div_two n
    have h2 : 2 * M n ≤ n + 1 := by omega
    nlinarith

/-- **Punctured Moser Parametric Bound on $M(n)$**: for all $n \ge 2$ and $R \in \mathbb{N}$,
combining `punctured_parabolic_bathtub_overlap_inequality`, `moser_shifted_second_moment_identity`,
`four_mul_M_le_sq`, and the variance-shift dominance $(n q_0)^2 \le 2\Delta^2 + 2(n q_0 - \Delta)^2$
absorbs the shift penalty $24 q_0^2 M(n)$ into $12\Delta^2$ and yields:
`24 R^2 n^2 + 24 R^2 M n ≤ 16 n^4 + 5 n^2 + 8 R (4 R^2 - 1) M n`. -/
theorem punctured_moser_parametric_le_M {n : ℕ} (hn : 2 ≤ n) (R : ℕ) :
    24 * R ^ 2 * n ^ 2 + 24 * R ^ 2 * M n ≤
      16 * n ^ 4 + 5 * n ^ 2 + 8 * R * (4 * R ^ 2 - 1) * M n := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  · have hn1 : 1 ≤ n := by omega
    have hne : ({MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
        (_disjoint : Disjoint A B)
        (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
        (_same_card : A.card = B.card)}).Nonempty := by
      refine ⟨_, Finset.Icc (1 : ℤ) n, Finset.Icc (1 : ℤ) (2 * n) \ Finset.Icc (1 : ℤ) n,
        Finset.disjoint_sdiff, ?_, ?_, rfl⟩
      · exact Finset.union_sdiff_of_subset (Finset.Icc_subset_Icc le_rfl (by omega))
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.Icc_subset_Icc le_rfl (by omega)),
          Int.card_Icc, Int.card_Icc]
        omega
    obtain ⟨A, B, hdisj, hunion, hsame, hM⟩ := Nat.sInf_mem hne
    have hA_sub : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
    have hB_sub : B ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_right
    have hcard_sum : A.card + B.card = 2 * n := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Int.card_Icc]
      omega
    have hA : A.card = n := by omega
    have hB : B.card = n := by omega
    have hM_eq : MaxOverlap A B = M n := hM
    have h4M : 4 * (MaxOverlap A B : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [hM_eq]
      exact_mod_cast four_mul_M_le_sq hn
    set Δℤ : ℤ := (∑ a ∈ A, a) - (∑ b ∈ B, b)
    obtain ⟨q₀, hq₀⟩ := exists_int_nearest_mul_le hn1 Δℤ
    set Δ : ℝ := (∑ a ∈ A, (a : ℝ)) - (∑ b ∈ B, (b : ℝ))
    have hq₀_real : 4 * ((n : ℝ) * (q₀ : ℝ) - Δ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hcast : ((n : ℤ) * q₀ - Δℤ : ℝ) = (n : ℝ) * (q₀ : ℝ) - Δ := by
        dsimp [Δℤ, Δ]; push_cast; ring
      have hq_cast : (4 * ((n : ℤ) * q₀ - Δℤ) ^ 2 : ℝ) ≤ ((n : ℤ) ^ 2 : ℝ) := by
        exact_mod_cast hq₀
      push_cast at hq_cast
      rw [← hcast]
      exact hq_cast
    have hdom : 6 * (n : ℝ) ^ 2 * (q₀ : ℝ) ^ 2 ≤
        12 * Δ ^ 2 + 12 * ((n : ℝ) * (q₀ : ℝ) - Δ) ^ 2 := by
      linarith [sq_nonneg (2 * Δ - (n : ℝ) * (q₀ : ℝ))]
    have hq_mul : 24 * (q₀ : ℝ) ^ 2 * (MaxOverlap A B : ℝ) ≤
        6 * (n : ℝ) ^ 2 * (q₀ : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (q₀ : ℝ)]
    have hmax_ge : (R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2 ≤ max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) :=
      le_max_right 0 _
    have hmax_mul : 24 * ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) * (MaxOverlap A B : ℝ) ≤
        24 * max 0 ((R : ℝ) ^ 2 - (q₀ : ℝ) ^ 2) * (MaxOverlap A B : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (MaxOverlap A B : ℝ) by positivity]
    have hshift := moser_shifted_second_moment_identity hdisj hunion hA hB (q₀ : ℝ)
    have hbat := punctured_parabolic_bathtub_overlap_inequality hdisj hA_sub hB_sub hA hB q₀ R
    have hreal : 24 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 + 24 * (R : ℝ) ^ 2 * (M n : ℝ) ≤
        16 * (n : ℝ) ^ 4 + 5 * (n : ℝ) ^ 2 +
          8 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (M n : ℝ) := by
      rw [← hM_eq]
      dsimp [Δ] at hq₀_real hdom
      linarith
    have h4R2 : 1 ≤ 4 * R ^ 2 := by nlinarith
    have hcast_lhs : ((24 * R ^ 2 * n ^ 2 + 24 * R ^ 2 * M n : ℕ) : ℝ) =
        24 * (R : ℝ) ^ 2 * (n : ℝ) ^ 2 + 24 * (R : ℝ) ^ 2 * (M n : ℝ) := by
      push_cast; ring
    have hcast_rhs : ((16 * n ^ 4 + 5 * n ^ 2 + 8 * R * (4 * R ^ 2 - 1) * M n : ℕ) : ℝ) =
        16 * (n : ℝ) ^ 4 + 5 * (n : ℝ) ^ 2 +
          8 * (R : ℝ) * (4 * (R : ℝ) ^ 2 - 1) * (M n : ℝ) := by
      push_cast [Nat.cast_sub h4R2]; ring
    rw [← hcast_lhs, ← hcast_rhs] at hreal
    exact_mod_cast hreal

/-- Exact evaluation `M 8 = 4`, proved algebraically from `punctured_moser_parametric_le_M`
at $n = 8, R = 11$ (which refutes $M(8) \le 3$ via $194568 > 193368$, whereas un-punctured
Moser only gave $M(8) \ge 3$) and `M_eight_le_four`. -/
theorem M_eight_eq_four : M 8 = 4 := by
  have hlb := punctured_moser_parametric_le_M (n := 8) (by omega) 11
  have hub := M_eight_le_four
  omega

/-- Exact evaluation `M 14 = 6`, proved algebraically without `decide` by combining
`punctured_moser_parametric_le_M` at $n = 14, R = 19$ (refuting $M(14) \le 5$ via
$1741464 > 1712316$) with Fekete 2-fold block inflation `M (7 * 2) ≤ 2 * M 7 = 6`. -/
theorem M_fourteen_eq_six : M 14 = 6 := by
  have hlb := punctured_moser_parametric_le_M (n := 14) (by omega) 19
  have hub : M 14 ≤ 6 := by
    have h := M_mul_le_mul_M 7 2
    rw [M_seven_eq_three] at h
    omega
  omega

/-- **Scherk's Strict Asymptotic Lower Bound (`minimum_overlap.variants.lower.scherk_1955`)**:
`1 - (Real.sqrt 2)⁻¹ < atTop.liminf MinOverlapQuotient`. -/
theorem minimum_overlap_variants_lower_scherk_1955 :
    1 - (Real.sqrt 2)⁻¹ < atTop.liminf MinOverlapQuotient :=
  lt_of_lt_of_le erdos_lt_scherk_lt_moser_lt_mrs.2.1 moser_sqrt_two_div_four_le_liminf

/-- **Świerczkowski's (1958) Strict Asymptotic Lower Bound (`minimum_overlap.variants.lower.swierczkowski_1958`)**:
`(4 - 6 ^ ((1 : ℝ) / 2)) / 5 < atTop.liminf MinOverlapQuotient` ($\approx 0.31010205 < 0.35355339$). -/
theorem minimum_overlap_variants_lower_swierczkowski_1958 :
    (4 - 6 ^ ((1 : ℝ) / 2)) / 5 < atTop.liminf MinOverlapQuotient := by
  refine lt_of_lt_of_le ?_ moser_sqrt_two_div_four_le_liminf
  have h2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2_gt : (7 : ℝ) / 5 < Real.sqrt 2 := by nlinarith
  have h6_sq : ((6 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 6 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have h6_sqrt_eq : Real.sqrt 6 = 6 ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow 6
    rw [← h6_sqrt_eq]
    exact hsq
  have h6_pos : (0 : ℝ) < 6 ^ ((1 : ℝ) / 2) := by positivity
  have h6_gt : (12 : ℝ) / 5 < 6 ^ ((1 : ℝ) / 2) := by
    nlinarith [h6_pos, h6_sq]
  linarith
end Erdos36.Proofs
