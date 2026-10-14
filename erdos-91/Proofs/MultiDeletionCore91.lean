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

public import Mathlib
public import HexagonMultiplicity91

@[expose] public section

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators

namespace Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
open Finset Minimizer91 PlateauDefinitions91
open Erdos91.TriangularLatticeHexagonAndSub130Majority (triPoint triPoint_injective triNormSq triNorm card_image_triNorm_eq_card_image_triNormSq triOffset dist_triPoint_sq_eq_triNormSq dist_triPoint_eq hexRowList hexCoordsList hexCoords hexSet card_hexCoords card_hexSet mem_hexCoords triUtpRowList triUtpList triUtp card_triUtp_le mem_triUtp_of_bounds triOffset_mem_triUtp distanceSet_hexSet_subset triUtpFold mem_triUtp_iff card_triUtp_two_mul_le hexCompFold mem_hexCoords_iff)

theorem card_hexCoords_regular_eq (R : ℕ) :
    (hexCoords (2 * R + 1) R (2 * R)).card = 3 * R * (R + 1) + 1 := by
  have h := card_hexSet_regular_eq R
  unfold hexSet at h
  rwa [Finset.card_image_of_injective _ triPoint_injective] at h

def triUtpUnfold (R : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  if ab.1 ≤ ab.2 then ab else (ab.2, 2 * R + 1 - ab.1)

theorem triUtpFold_unfold (R : ℕ) {ab : ℕ × ℕ}
    (hab : ab ∈ (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).erase (0, 0)) :
    triUtpFold R (triUtpUnfold R ab) = ab := by
  rcases ab with ⟨a, b⟩
  simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq] at hab
  unfold triUtpUnfold triUtpFold
  dsimp
  split_ifs with h1 h2 h3
  · rfl
  · omega
  · omega
  · exact Prod.ext (by omega) (by omega)

theorem triUtpUnfold_mem_triUtp (R : ℕ) {ab : ℕ × ℕ}
    (hab : ab ∈ (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).erase (0, 0)) :
    triUtpUnfold R ab ∈ triUtp (2 * R) := by
  rcases ab with ⟨a, b⟩
  simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_range, ne_eq, Prod.mk.injEq] at hab
  rw [mem_triUtp_iff]
  unfold triUtpUnfold
  dsimp
  split_ifs with h1
  · refine ⟨by simp only [Prod.mk.injEq]; omega, h1, by omega⟩
  · refine ⟨by simp only [Prod.mk.injEq]; omega, by omega, by omega⟩

theorem sq_erase_subset_image_triUtpFold (R : ℕ) :
    (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).erase (0, 0) ⊆
      (triUtp (2 * R)).image (triUtpFold R) := by
  intro ab hab
  exact Finset.mem_image.mpr ⟨triUtpUnfold R ab, triUtpUnfold_mem_triUtp R hab, triUtpFold_unfold R hab⟩

/-- **Exact symbolic cardinality of `triUtp (2 * R)`:**
for every `R : ℕ`, `(triUtp (2 * R)).card = R * (R + 2)`. -/
theorem card_triUtp_two_mul_eq (R : ℕ) :
    (triUtp (2 * R)).card = R * (R + 2) := by
  have hhi := card_triUtp_two_mul_le R
  have hlo1 := Finset.card_le_card (sq_erase_subset_image_triUtpFold R)
  have hmem0 : ((0, 0) : ℕ × ℕ) ∈ Finset.range (R + 1) ×ˢ Finset.range (R + 1) := by simp
  have hSq_card : ((Finset.range (R + 1) ×ˢ Finset.range (R + 1)).erase (0, 0)).card = R * (R + 2) := by
    have h1 := Finset.card_erase_add_one hmem0
    rw [Finset.card_product, Finset.card_range] at h1
    have hexp : (R + 1) * (R + 1) = R * (R + 2) + 1 := by ring
    omega
  rw [hSq_card] at hlo1
  have hlo := hlo1.trans Finset.card_image_le
  omega

theorem mem_hexCoords_base_anchor (R : ℕ) :
    (R, 0) ∈ hexCoords (2 * R + 1) R (2 * R) := by
  rw [mem_hexCoords_iff]
  dsimp
  omega

theorem mem_hexCoords_offset_of_mem_triUtp (R : ℕ) {u : ℕ × ℕ} (hu : u ∈ triUtp (2 * R)) :
    (R + u.1, u.2) ∈ hexCoords (2 * R + 1) R (2 * R) := by
  obtain ⟨_, hle, hsum⟩ := (mem_triUtp_iff (2 * R) u).mp hu
  rw [mem_hexCoords_iff]
  dsimp
  omega

theorem triOffset_base_anchor_eq (R : ℕ) {u : ℕ × ℕ} (hu : u.1 ≤ u.2) :
    triOffset (R, 0) (R + u.1, u.2) = u := by
  rcases u with ⟨x, y⟩
  dsimp at hu
  unfold triOffset
  dsimp
  have hdx : Nat.dist R (R + x) = x := by unfold Nat.dist; omega
  have hdy : Nat.dist 0 y = y := by unfold Nat.dist; omega
  rw [hdx, hdy]
  split_ifs <;> first | rfl | (apply Prod.ext <;> omega)

theorem dist_triPoint_base_anchor_eq (R : ℕ) {u : ℕ × ℕ} (hu : u.1 ≤ u.2) :
    dist (triPoint (R, 0)) (triPoint (R + u.1, u.2)) = triNorm u := by
  rw [dist_triPoint_eq (R, 0) (R + u.1, u.2), triOffset_base_anchor_eq R hu]

/-- **Exact symbolic distance-set identity on `hexSet (2R + 1) R (2R)`:**
for every `R : ℕ`, `distanceSet (hexSet (2 * R + 1) R (2 * R)) = (triUtp (2 * R)).image triNorm`. -/
theorem distanceSet_hexSet_regular_eq (R : ℕ) :
    Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R)) =
      (triUtp (2 * R)).image triNorm := by
  classical
  apply Finset.Subset.antisymm (distanceSet_hexSet_subset (2 * R + 1) R (2 * R) (by omega))
  intro r hr
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hne0, hle, _⟩ := (mem_triUtp_iff (2 * R) u).mp hu
  have hp : triPoint (R, 0) ∈ hexSet (2 * R + 1) R (2 * R) :=
    Finset.mem_image_of_mem triPoint (mem_hexCoords_base_anchor R)
  have hq : triPoint (R + u.1, u.2) ∈ hexSet (2 * R + 1) R (2 * R) :=
    Finset.mem_image_of_mem triPoint (mem_hexCoords_offset_of_mem_triUtp R hu)
  have hpq : triPoint (R, 0) ≠ triPoint (R + u.1, u.2) := by
    intro heq
    have hinj := triPoint_injective heq
    simp only [Prod.mk.injEq] at hinj
    exact hne0 (Prod.ext (by omega) (by omega))
  exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
    ⟨triPoint (R, 0), hp, triPoint (R + u.1, u.2), hq, hpq, dist_triPoint_base_anchor_eq R hle⟩

/-- **Exact combinatorial distance-count formula on `hexSet (2R + 1) R (2R)`:**
for every `R : ℕ`, `distinctDistances (hexSet (2 * R + 1) R (2 * R)) = ((triUtp (2 * R)).image triNormSq).card`. -/
theorem distinctDistances_hexSet_regular_eq (R : ℕ) :
    distinctDistances (hexSet (2 * R + 1) R (2 * R)) =
      ((triUtp (2 * R)).image triNormSq).card := by
  change (Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R))).card = _
  rw [distanceSet_hexSet_regular_eq R, card_image_triNorm_eq_card_image_triNormSq]


end Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet

namespace Erdos91.ExactHexagonDistanceCountsR1To18
open Erdos91.TriangularLatticeHexagonAndSub130Majority Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet Minimizer91

theorem card_hexSet_regular_2 : (hexSet 5 2 4).card = 19 :=
  card_hexSet_regular_eq 2

theorem distinctDistances_hexSet_regular_2 :
    distinctDistances (hexSet 5 2 4) = 8 := by
  rw [distinctDistances_hexSet_regular_eq 2]
  rfl

end Erdos91.ExactHexagonDistanceCountsR1To18

namespace Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions
open Erdos91.TriangularLatticeHexagonAndSub130Majority

theorem mem_insert_zero_triUtp_bounds (R : ℕ) {u : ℕ × ℕ}
    (hu : u ∈ insert (0, 0) (triUtp R)) :
    u.1 ≤ u.2 ∧ u.1 + u.2 ≤ R := by
  rcases Finset.mem_insert.mp hu with rfl | hutp
  · exact ⟨by omega, by omega⟩
  · obtain ⟨_, hle, hsum⟩ := (mem_triUtp_iff R u).mp hutp
    exact ⟨hle, hsum⟩

end Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions

/-! ## Sum-of-two-squares sieve -/

/-!
# Modular Sum-of-Two-Squares CRT Sieve and `χ₄` Euler Product Quotient for Erdős #91

This module establishes the number-theoretic heart of the sublinear upper bound
`d(n) = o(n)` (`SublinearMinimalDistances`) for planar distinct distances:

1. **Modulo-`4` Dirichlet character Euler product quotient (`exists_primesBelow_sieve_product_lt`):**
   Using the nontrivial quadratic character `chi4 : DirichletCharacter ℂ 4` (`χ₄(1) = 1`, `χ₄(3) = -1`),
   we compare `∏_{p < n, p ≡ 3 (mod 4)} ((p^2 - p + 1) / p^2)^3` against the Euler-product quotient
   for `L(s, χ₄) / ζ(s)` at real `s > 1`. Since `L(s, χ₄) / ζ(s) → 0` as `s → 1+`, for every
   `C : ℕ` there exists `n : ℕ` such that `Q = {p ∈ n.primesBelow | p % 4 = 3}` satisfies
   `2 * (C + 1) * ∏_{p ∈ Q} (p^2 - p + 1) < ∏_{p ∈ Q} p^2`.
2. **Prime `p ≡ 3 (mod 4)` square-divisibility and CRT sieve (`exists_sieve_bound_for_C`):**
   Every integer `m = x^2 + y^2` satisfies `sieveGood p m` (`m % p ≠ 0 ∨ m % p^2 = 0`) for every
   prime `p ≡ 3 (mod 4)`. By Chinese Remainder Theorem induction over `Q`, the number of sums of
   two squares in `Finset.range (2 * k^2)` is at most `(2 * k^2 / M + 1) * W`, where
   `M = ∏_{p ∈ Q} p^2` and `W = ∏_{p ∈ Q} (p^2 - p + 1)`.
-/

namespace Erdos91.SumOfTwoSquaresSieve

open Complex Filter Topology Finset

/-- The nontrivial quadratic Dirichlet character modulo `4`, valued in `ℂ`. -/
noncomputable def chi4 : DirichletCharacter ℂ 4 :=
  MulChar.ringHomComp ZMod.χ₄ (Int.castRingHom ℂ)

theorem chi4_ne_one : chi4 ≠ 1 := by
  intro h
  have h3 : chi4 3 = (1 : DirichletCharacter ℂ 4) 3 := congrFun (congrArg DFunLike.coe h) 3
  have h1 : chi4 3 = -1 := by simp [chi4, ZMod.χ₄]
  have h2 : (1 : DirichletCharacter ℂ 4) 3 = 1 :=
    MulChar.one_apply (by decide : IsUnit (3 : ZMod 4))
  rw [h1, h2] at h3
  norm_num at h3

theorem chi4_apply_of_mod_four_eq_one {p : ℕ} (hp : p % 4 = 1) : chi4 (p : ZMod 4) = 1 := by
  change (ZMod.χ₄ (p : ZMod 4) : ℂ) = 1
  rw [ZMod.χ₄_nat_one_mod_four hp]
  norm_num

theorem chi4_apply_of_mod_four_eq_three {p : ℕ} (hp : p % 4 = 3) : chi4 (p : ZMod 4) = -1 := by
  change (ZMod.χ₄ (p : ZMod 4) : ℂ) = -1
  rw [ZMod.χ₄_nat_three_mod_four hp]
  norm_num

theorem chi4_apply_two : chi4 ((2 : ℕ) : ZMod 4) = 0 := by
  simp [chi4, ZMod.χ₄]

theorem nat_cpow_neg_real (p : ℕ) (x : ℝ) :
    (p : ℂ) ^ (-(x : ℂ)) = (((p : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [← ofReal_natCast, ← ofReal_neg, ofReal_cpow (Nat.cast_nonneg p)]

/-- Cubic polynomial inequality `((p^2 - p + 1) / p^2)^3 ≤ (p - 1) / (p + 1)` for all `p ≥ 3`. -/
theorem cube_sieve_factor_le_ratio {p : ℕ} (hp : 3 ≤ p) :
    (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 3 ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hp_real : (3 : ℝ) ≤ p := Nat.ofNat_le_cast.mpr hp
  have hsub : ((p ^ 2 - p + 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - (p : ℝ) + 1 := by
    have hle : p ≤ p ^ 2 := by nlinarith
    push_cast [hle]
    ring
  rw [hsub, Nat.cast_pow, div_pow, div_le_div_iff₀ (by positivity) (by linarith)]
  have hid : ((p : ℝ) - 1) * ((p : ℝ) ^ 2) ^ 3 - ((p : ℝ) ^ 2 - (p : ℝ) + 1) ^ 3 * ((p : ℝ) + 1) =
      ((p : ℝ) - 3) * ((p : ℝ) ^ 5 + (p : ℝ) ^ 3 + 4 * (p : ℝ) ^ 2 + 9 * (p : ℝ) + 29) + 86 := by
    ring
  have hpos : 0 ≤ ((p : ℝ) - 3) * ((p : ℝ) ^ 5 + (p : ℝ) ^ 3 + 4 * (p : ℝ) ^ 2 + 9 * (p : ℝ) + 29) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

/-- Pointwise Euler-factor comparison for `L(x, χ₄) / ζ(x)` at prime `p` and real `x > 1`. -/
theorem euler_factor_ratio_bound {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x) :
    (if p = 2 then (1 / 2 : ℝ) else 1) *
      (if p % 4 = 3 then (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 3 else 1) ≤
      ‖(1 - chi4 (p : ZMod 4) * (p : ℂ) ^ (-(x : ℂ)))⁻¹ / (1 - (p : ℂ) ^ (-(x : ℂ)))⁻¹‖ := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp_gt1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr hp.one_lt
  have hpow_pos : 0 < (p : ℝ) ^ (-x) := Real.rpow_pos_of_pos hp_pos (-x)
  have hpow_le_inv : (p : ℝ) ^ (-x) ≤ (p : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp_gt1.le (by linarith)
  have hinv_lt1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
  have hpow_lt1 : (p : ℝ) ^ (-x) < 1 := hpow_le_inv.trans_lt hinv_lt1
  have hc1 : (1 : ℂ) - (((p : ℝ) ^ (-x) : ℝ) : ℂ) = (((1 - (p : ℝ) ^ (-x)) : ℝ) : ℂ) := by push_cast; ring
  rw [div_inv_eq_mul, inv_mul_eq_div, norm_div, nat_cpow_neg_real]
  rcases hp.eq_two_or_odd with rfl | hodd
  · have h23 : ¬ ((2 : ℕ) % 4 = 3) := by decide
    simp only [↓reduceIte, h23, mul_one]
    rw [chi4_apply_two, zero_mul, sub_zero, norm_one, div_one,
      hc1, norm_real, Real.norm_of_nonneg (by linarith)]
    norm_num at hpow_le_inv
    linarith
  · have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hmod4 with h1 | h3
    · have hp2 : p ≠ 2 := by omega
      have h13 : ¬ (p % 4 = 3) := by omega
      simp only [hp2, h13, ↓reduceIte, mul_one]
      rw [chi4_apply_of_mod_four_eq_one h1, one_mul]
      have hne : ‖(1 : ℂ) - (((p : ℝ) ^ (-x) : ℝ) : ℂ)‖ ≠ 0 := by
        rw [hc1, norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      rw [div_self hne]
    · have hp2 : p ≠ 2 := by omega
      have hp3 : 3 ≤ p := by omega
      simp only [hp2, h3, ↓reduceIte, one_mul]
      rw [chi4_apply_of_mod_four_eq_three h3, neg_one_mul, sub_neg_eq_add]
      have hc2 : (1 : ℂ) + (((p : ℝ) ^ (-x) : ℝ) : ℂ) = (((1 + (p : ℝ) ^ (-x)) : ℝ) : ℂ) := by push_cast; ring
      rw [hc1, hc2, norm_real, norm_real,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
      refine (cube_sieve_factor_le_ratio hp3).trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      have hpinv : (p : ℝ) * (p : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hp_pos.ne'
      nlinarith

theorem prod_ite_eq_two_ge_half (s : Finset ℕ) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ s, (if p = 2 then (1 / 2 : ℝ) else 1) := by
  rw [← Finset.prod_filter, Finset.prod_const]
  have hsub : s.filter (· = 2) ⊆ {2} := by
    intro x hx
    exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hx).2
  have hcard : (s.filter (· = 2)).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  have h01 : (s.filter (· = 2)).card = 0 ∨ (s.filter (· = 2)).card = 1 := by omega
  rcases h01 with h0 | h1 <;> [rw [h0]; rw [h1]] <;> norm_num

theorem prod_sieve_cube_le_norm_euler_quotient (n : ℕ) {x : ℝ} (hx : 1 < x) :
    let Q := (n.primesBelow).filter (fun p => p % 4 = 3)
    (1 / 2 : ℝ) * (∏ p ∈ Q, (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ))) ^ 3 ≤
      ‖(∏ p ∈ n.primesBelow, (1 - chi4 (p : ZMod 4) * (p : ℂ) ^ (-(x : ℂ)))⁻¹) /
        (∏ p ∈ n.primesBelow, (1 - (p : ℂ) ^ (-(x : ℂ)))⁻¹)‖ := by
  intro Q
  have hprod_le :
      ∏ p ∈ n.primesBelow,
        ((if p = 2 then (1 / 2 : ℝ) else 1) *
          (if p % 4 = 3 then (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 3 else 1)) ≤
      ∏ p ∈ n.primesBelow,
        ‖(1 - chi4 (p : ZMod 4) * (p : ℂ) ^ (-(x : ℂ)))⁻¹ / (1 - (p : ℂ) ^ (-(x : ℂ)))⁻¹‖ := by
    gcongr with p hp
    exact euler_factor_ratio_bound (Nat.prime_of_mem_primesBelow hp) hx
  rw [Finset.prod_mul_distrib] at hprod_le
  have hfilt :
      (∏ p ∈ n.primesBelow,
        if p % 4 = 3 then (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ)) ^ 3 else 1) =
      (∏ p ∈ Q, (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ))) ^ 3 := by
    rw [← Finset.prod_filter, Finset.prod_pow]
  rw [hfilt] at hprod_le
  rw [← Finset.prod_div_distrib, norm_prod]
  refine le_trans ?_ hprod_le
  exact mul_le_mul_of_nonneg_right (prod_ite_eq_two_ge_half n.primesBelow) (by positivity)

theorem tendsto_LFunction_div_riemannZeta_nhds_one :
    Tendsto (fun s : ℂ => DirichletCharacter.LFunction chi4 s / riemannZeta s)
      (𝓝[≠] 1) (𝓝 0) := by
  have hL : Tendsto (DirichletCharacter.LFunction chi4) (𝓝[≠] 1)
      (𝓝 (DirichletCharacter.LFunction chi4 1)) :=
    (DirichletCharacter.differentiable_LFunction chi4_ne_one).continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hsub : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have h0 : (1 : ℂ) - 1 = 0 := sub_self 1
    rw [← h0]
    exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction chi4 s) (𝓝[≠] 1) (𝓝 0) := by
    simpa using hsub.mul hL
  have hq := hnum.div riemannZeta_residue_one one_ne_zero
  simp only [zero_div] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
  exact mul_div_mul_left (DirichletCharacter.LFunction chi4 s) (riemannZeta s) hs0

/-- For every `C : ℕ`, there exists a prime cutoff `n : ℕ` such that the primes `p < n` with
`p % 4 = 3` have sieve density `< 1 / (2 * (C + 1))`. -/
theorem exists_primesBelow_sieve_product_lt (C : ℕ) :
    ∃ n : ℕ,
      let Q := (n.primesBelow).filter (fun p => p % 4 = 3)
      2 * (C + 1) * (∏ p ∈ Q, (p ^ 2 - p + 1)) < ∏ p ∈ Q, p ^ 2 := by
  have hB3_pos : (0 : ℝ) < (1 / (2 * (C : ℝ) + 2)) ^ 3 := by positivity
  let ε : ℝ := (1 / 4 : ℝ) * (1 / (2 * (C : ℝ) + 2)) ^ 3
  have hε : 0 < ε := by positivity
  have hlim_norm : Tendsto (fun s : ℂ => ‖DirichletCharacter.LFunction chi4 s / riemannZeta s‖)
      (𝓝[≠] 1) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp tendsto_LFunction_div_riemannZeta_nhds_one
  have hev_s : ∀ᶠ s : ℂ in 𝓝[≠] 1, ‖DirichletCharacter.LFunction chi4 s / riemannZeta s‖ < ε :=
    hlim_norm.eventually (Iio_mem_nhds hε)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev_s
  obtain ⟨δ, hδ_pos, hδ⟩ := hev_s
  let x : ℝ := 1 + min (δ / 2) 1
  have hx_gt1 : 1 < x := by
    dsimp [x]
    have : 0 < min (δ / 2) 1 := lt_min (by linarith) zero_lt_one
    linarith
  have hdist : dist (x : ℂ) 1 < δ := by
    rw [dist_eq_norm, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
    have : x - 1 ≤ δ / 2 := by dsimp [x]; linarith [min_le_left (δ / 2) 1]
    linarith
  have hx_ne1 : (x : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, ← ofReal_one, ne_eq, ofReal_inj]
    linarith
  have hquot_lt : ‖DirichletCharacter.LFunction chi4 (x : ℂ) / riemannZeta (x : ℂ)‖ < ε :=
    hδ hdist hx_ne1
  have hs_re : 1 < ((x : ℂ)).re := by simpa using hx_gt1
  have hzeta_ne0 : riemannZeta (x : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs_re.le
  have hL_eq : DirichletCharacter.LFunction chi4 (x : ℂ) = LSeries (fun m => chi4 m) (x : ℂ) :=
    DirichletCharacter.LFunction_eq_LSeries chi4 hs_re
  have hE_L := DirichletCharacter.LSeries_eulerProduct chi4 hs_re
  rw [← hL_eq] at hE_L
  have hE_z := riemannZeta_eulerProduct hs_re
  have hE_div := (continuous_norm.tendsto _).comp (hE_L.div hE_z hzeta_ne0)
  have hev_n := hE_div.eventually (Iio_mem_nhds hquot_lt)
  obtain ⟨n, hn⟩ := hev_n.exists
  dsimp at hn
  refine ⟨n, ?_⟩
  intro Q
  have hbound : (1 / 2 : ℝ) * (∏ p ∈ Q, (((p ^ 2 - p + 1 : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ))) ^ 3 < ε :=
    (prod_sieve_cube_le_norm_euler_quotient n hx_gt1).trans_lt hn
  have hpos_den : (0 : ℝ) < ∏ p ∈ Q, ((p ^ 2 : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
    exact Nat.cast_pos.mpr (pow_pos hp_prime.pos 2)
  rw [Finset.prod_div_distrib] at hbound
  have hpow_lt : ((∏ p ∈ Q, ((p ^ 2 - p + 1 : ℕ) : ℝ)) / (∏ p ∈ Q, ((p ^ 2 : ℕ) : ℝ))) ^ 3 <
      (1 / (2 * (C : ℝ) + 2)) ^ 3 := by
    change (1 / 2 : ℝ) * ((∏ p ∈ Q, ((p ^ 2 - p + 1 : ℕ) : ℝ)) / (∏ p ∈ Q, ((p ^ 2 : ℕ) : ℝ))) ^ 3 <
      (1 / 4 : ℝ) * (1 / (2 * (C : ℝ) + 2)) ^ 3 at hbound
    linarith
  have hbase_lt : (∏ p ∈ Q, ((p ^ 2 - p + 1 : ℕ) : ℝ)) / (∏ p ∈ Q, ((p ^ 2 : ℕ) : ℝ)) <
      1 / (2 * (C : ℝ) + 2) := by
    by_contra hge
    push Not at hge
    have h3 : (1 / (2 * (C : ℝ) + 2)) ^ 3 ≤
        ((∏ p ∈ Q, ((p ^ 2 - p + 1 : ℕ) : ℝ)) / (∏ p ∈ Q, ((p ^ 2 : ℕ) : ℝ))) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hge 3
    linarith
  rw [div_lt_div_iff₀ hpos_den (by positivity)] at hbase_lt
  have hcast : ((2 * (C + 1) * ∏ p ∈ Q, (p ^ 2 - p + 1) : ℕ) : ℝ) <
      ((∏ p ∈ Q, p ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Nat.cast_prod, Nat.cast_prod]
    linarith
  exact_mod_cast hcast

/-- Modulo-`p^2` condition satisfied by every sum of two squares at a prime `p ≡ 3 (mod 4)`:
either `p ∤ m` or `p^2 ∣ m`. -/
def sieveGood (p m : ℕ) : Prop :=
  m % p ≠ 0 ∨ m % (p ^ 2) = 0

instance (p m : ℕ) : Decidable (sieveGood p m) := by
  unfold sieveGood; infer_instance

theorem sieveGood_mod_sq (p m : ℕ) :
    sieveGood p (m % (p ^ 2)) ↔ sieveGood p m := by
  unfold sieveGood
  have hdvd : p ∣ p ^ 2 := ⟨p, sq p⟩
  rw [Nat.mod_mod_of_dvd m hdvd, Nat.mod_mod]

theorem sieveGood_mod_of_dvd {p M : ℕ} (h : p ^ 2 ∣ M) (m : ℕ) :
    sieveGood p (m % M) ↔ sieveGood p m := by
  unfold sieveGood
  have hp : p ∣ M := dvd_trans ⟨p, sq p⟩ h
  rw [Nat.mod_mod_of_dvd m hp, Nat.mod_mod_of_dvd m h]

/-- Every sum of two squares `x^2 + y^2` satisfies `sieveGood p (x^2 + y^2)` for every prime `p ≡ 3 (mod 4)`. -/
theorem sieveGood_sq_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (x y : ℕ) :
    sieveGood p (x ^ 2 + y ^ 2) := by
  unfold sieveGood
  by_cases hdiv : (x ^ 2 + y ^ 2) % p = 0
  · right
    have hdvd : p ∣ x ^ 2 + y ^ 2 := Nat.dvd_of_mod_eq_zero hdiv
    have : Fact p.Prime := ⟨hp⟩
    have hz : ((x : ZMod p) ^ 2 + (y : ZMod p) ^ 2) = 0 := by
      have hcast : (((x ^ 2 + y ^ 2 : ℕ) : ZMod p)) = 0 :=
        (ZMod.natCast_eq_zero_iff (x ^ 2 + y ^ 2) p).mpr hdvd
      push_cast at hcast
      exact hcast
    have hsq : (x : ZMod p) ^ 2 = - (y : ZMod p) ^ 2 :=
      eq_neg_of_add_eq_zero_left hz
    have hy0 : (y : ZMod p) = 0 := by
      by_contra hy_ne
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy_ne hsq hp3
    have hpy : p ∣ y := (ZMod.natCast_eq_zero_iff y p).mp hy0
    have hpy2 : p ^ 2 ∣ y ^ 2 := pow_dvd_pow_of_dvd hpy 2
    have hpx2_p : p ∣ x ^ 2 := (Nat.dvd_add_left (dvd_trans ⟨p, sq p⟩ hpy2)).mp hdvd
    have hpx : p ∣ x := hp.dvd_of_dvd_pow hpx2_p
    have hpx2 : p ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd hpx 2
    exact Nat.mod_eq_zero_of_dvd (dvd_add hpx2 hpy2)
  · exact Or.inl hdiv

theorem card_filter_not_sieveGood (p : ℕ) (hp : 2 ≤ p) :
    ((range (p ^ 2)).filter (fun r => ¬ sieveGood p r)).card = p - 1 := by
  have heq : (range (p ^ 2)).filter (fun r => ¬ sieveGood p r) =
      (Ico 1 p).image (fun c => p * c) := by
    ext r
    simp only [mem_filter, mem_range, sieveGood, not_or, not_ne_iff, mem_image, mem_Ico]
    constructor
    · rintro ⟨hr, hmodp, hmodp2⟩
      have hmul : p * (r / p) = r := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmodp)
      have hlt : r / p < p := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [sq] using hr)
      refine ⟨r / p, ⟨?_, hlt⟩, hmul⟩
      rcases eq_or_ne (r / p) 0 with h0 | hne
      · rw [h0, mul_zero] at hmul
        subst hmul
        exact (hmodp2 (Nat.zero_mod _)).elim
      · exact Nat.pos_of_ne_zero hne
    · rintro ⟨c, ⟨hc1, hcp⟩, rfl⟩
      refine ⟨by nlinarith, Nat.mul_mod_right p c, ?_⟩
      intro hdiv2
      have hdvd2 : p * p ∣ p * c := by simpa [sq] using Nat.dvd_of_mod_eq_zero hdiv2
      have hpc : p ∣ c := (mul_dvd_mul_iff_left (by omega : p ≠ 0)).mp hdvd2
      have hle : p ≤ c := Nat.le_of_dvd (by omega) hpc
      omega
  rw [heq, Finset.card_image_of_injective _ (fun a b h => mul_left_cancel₀ (by omega : p ≠ 0) h),
    Nat.card_Ico]

theorem card_filter_sieveGood (p : ℕ) (hp : 2 ≤ p) :
    ((range (p ^ 2)).filter (sieveGood p)).card = p ^ 2 - p + 1 := by
  have hpart := card_filter_add_card_filter_not (s := range (p ^ 2)) (p := sieveGood p)
  rw [card_range, card_filter_not_sieveGood p hp] at hpart
  have hle : p ≤ p ^ 2 := by nlinarith
  omega

def sieveGoodSet (Q : Finset ℕ) (m : ℕ) : Prop :=
  ∀ p ∈ Q, sieveGood p m

instance (Q : Finset ℕ) (m : ℕ) : Decidable (sieveGoodSet Q m) := by
  unfold sieveGoodSet; infer_instance

theorem crt_card_filter_mul {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : Nat.Coprime A B)
    (P1 P2 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2] :
    ((range (A * B)).filter (fun r => P1 (r % A) ∧ P2 (r % B))).card =
      ((range A).filter P1).card * ((range B).filter P2).card := by
  rw [← card_product]
  refine Finset.card_bij (fun r _ => (r % A, r % B)) ?_ ?_ ?_
  · intro r hr
    obtain ⟨_, h1, h2⟩ := mem_filter.mp hr
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hA), h1⟩,
      mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hB), h2⟩⟩
  · intro r1 hr1 r2 hr2 heq
    injection heq with h1 h2
    have hm1 : r1 ≡ r2 [MOD A] := h1
    have hm2 : r1 ≡ r2 [MOD B] := h2
    have hm : r1 ≡ r2 [MOD A * B] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm1, hm2⟩
    exact hm.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hr1).1) (mem_range.mp (mem_filter.mp hr2).1)
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨ha_lt, hP1a⟩ := mem_filter.mp ha
    obtain ⟨hb_lt, hP2b⟩ := mem_filter.mp hb
    let k := Nat.chineseRemainder hcop a b
    let r := k.val % (A * B)
    have hr_lt : r < A * B := Nat.mod_lt k.val (mul_pos hA hB)
    have hrA : r % A = a := by
      have h1 : r ≡ k.val [MOD A] := Nat.ModEq.of_mul_right B (Nat.mod_modEq k.val (A * B))
      have h2 : r ≡ a [MOD A] := h1.trans k.property.1
      rw [Nat.ModEq] at h2
      rw [h2, Nat.mod_eq_of_lt (mem_range.mp ha_lt)]
    have hrB : r % B = b := by
      have h1 : r ≡ k.val [MOD B] := Nat.ModEq.of_mul_left A (Nat.mod_modEq k.val (A * B))
      have h2 : r ≡ b [MOD B] := h1.trans k.property.2
      rw [Nat.ModEq] at h2
      rw [h2, Nat.mod_eq_of_lt (mem_range.mp hb_lt)]
    refine ⟨r, mem_filter.mpr ⟨mem_range.mpr hr_lt, ?_⟩, Prod.ext hrA hrB⟩
    rw [hrA, hrB]
    exact ⟨hP1a, hP2b⟩

theorem card_filter_sieveGoodSet (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ((range (∏ p ∈ Q, p ^ 2)).filter (sieveGoodSet Q)).card =
      ∏ p ∈ Q, (p ^ 2 - p + 1) := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    decide
  | @insert p s hps ih =>
    have hp : p.Prime := hQ p (mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hQ q (mem_insert_of_mem hq)
    rw [prod_insert hps, prod_insert hps, ← ih hs, ← card_filter_sieveGood p hp.two_le]
    have hA : 0 < p ^ 2 := pow_pos hp.pos 2
    have hB : 0 < ∏ q ∈ s, q ^ 2 := prod_pos (fun q hq => pow_pos (hs q hq).pos 2)
    have hcop : Nat.Coprime (p ^ 2) (∏ q ∈ s, q ^ 2) := by
      apply Nat.Coprime.pow_left 2
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      apply Nat.Coprime.pow_right 2
      exact (Nat.coprime_primes hp (hs q hq)).mpr (fun heq => hps (heq ▸ hq))
    rw [← crt_card_filter_mul hA hB hcop (sieveGood p) (sieveGoodSet s)]
    congr 1
    apply Finset.filter_congr
    intro r _
    simp only [sieveGoodSet, forall_mem_insert]
    rw [sieveGood_mod_sq]
    refine and_congr_right (fun _ => forall₂_congr (fun q hq => ?_))
    exact (sieveGood_mod_of_dvd (dvd_prod_of_mem (fun x => x ^ 2) hq) r).symm

theorem card_filter_range_sieveGoodSet_le (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (N : ℕ) :
    ((range N).filter (sieveGoodSet Q)).card ≤
      (N / (∏ p ∈ Q, p ^ 2) + 1) * (∏ p ∈ Q, (p ^ 2 - p + 1)) := by
  classical
  let M := ∏ p ∈ Q, p ^ 2
  have hM : 0 < M := prod_pos (fun p hp => pow_pos (hQ p hp).pos 2)
  rw [← card_filter_sieveGoodSet Q hQ, ← card_range (N / M + 1), ← card_product]
  have hinj : Set.InjOn (fun m => (m / M, m % M)) ((range N).filter (sieveGoodSet Q)) := by
    intro m1 _ m2 _ heq
    injection heq with hq hr
    rw [← Nat.div_add_mod m1 M, ← Nat.div_add_mod m2 M, hq, hr]
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hx
  obtain ⟨hmN, hgood⟩ := mem_filter.mp hm
  rw [mem_product, mem_range, mem_filter, mem_range]
  refine ⟨?_, Nat.mod_lt m hM, ?_⟩
  · have hle : m / M ≤ N / M := Nat.div_le_div_right (le_of_lt (mem_range.mp hmN))
    omega
  · intro p hp
    exact (sieveGood_mod_of_dvd (dvd_prod_of_mem (fun x => x ^ 2) hp) m).mpr (hgood p hp)

/-- Master sum-of-two-squares sieve bound: for every `C : ℕ`, there exist `M, W : ℕ` with
`0 < M` and `4 * C * W + W < M` such that for every `k ≥ 1`,
`M * #{m < 2k^2 : ∃ x y, m = x^2 + y^2} ≤ (2k^2 + M) * W`. -/
theorem exists_sieve_bound_for_C (C : ℕ) :
    ∃ M W : ℕ, 0 < M ∧ 4 * C * W + W < M ∧
      ∀ k : ℕ, 1 ≤ k →
        M * ((range (2 * k ^ 2)).filter (fun m => ∃ x y : ℕ, m = x ^ 2 + y ^ 2)).card ≤
          (2 * k ^ 2 + M) * W := by
  obtain ⟨n0, hn0⟩ := exists_primesBelow_sieve_product_lt (2 * C)
  let Q := (n0.primesBelow).filter (fun p => p % 4 = 3)
  have hQ_prime : ∀ p ∈ Q, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1
  have hQ_mod : ∀ p ∈ Q, p % 4 = 3 := fun p hp =>
    (Finset.mem_filter.mp hp).2
  let M := ∏ p ∈ Q, p ^ 2
  let W := ∏ p ∈ Q, (p ^ 2 - p + 1)
  change 2 * (2 * C + 1) * W < M at hn0
  have hM_pos : 0 < M := Finset.prod_pos (fun p hp => pow_pos (hQ_prime p hp).pos 2)
  have hMW : 4 * C * W + W < M := by nlinarith
  refine ⟨M, W, hM_pos, hMW, ?_⟩
  intro k _
  have hsub : (range (2 * k ^ 2)).filter (fun m => ∃ x y : ℕ, m = x ^ 2 + y ^ 2) ⊆
      (range (2 * k ^ 2)).filter (sieveGoodSet Q) := by
    intro m hm
    obtain ⟨hm_lt, x, y, rfl⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hm_lt, fun p hp => sieveGood_sq_add_sq (hQ_prime p hp) (hQ_mod p hp) x y⟩
  have hcard1 := (Finset.card_le_card hsub).trans (card_filter_range_sieveGoodSet_le Q hQ_prime (2 * k ^ 2))
  change ((range (2 * k ^ 2)).filter (fun m => ∃ x y : ℕ, m = x ^ 2 + y ^ 2)).card ≤
    (2 * k ^ 2 / M + 1) * W at hcard1
  have hmul := Nat.mul_le_mul_left M hcard1
  have hdiv : M * (2 * k ^ 2 / M) ≤ 2 * k ^ 2 := Nat.mul_div_le (2 * k ^ 2) M
  nlinarith

end Erdos91.SumOfTwoSquaresSieve


/-! ## Sublinear distance bounds -/

namespace Erdos91.SublinearMinimalDistancesProof

open Finset Filter Topology Minimizer91 MinimumMonotone91 Erdos91.SumOfTwoSquaresSieve

noncomputable def gridPoint (p : ℕ × ℕ) : Plane := !₂[(p.1 : ℝ), (p.2 : ℝ)]

theorem gridPoint_injective : Function.Injective gridPoint := by
  intro p q h
  have h0 : (p.1 : ℝ) = (q.1 : ℝ) := congrArg (fun x : Plane => x 0) h
  have h1 : (p.2 : ℝ) = (q.2 : ℝ) := congrArg (fun x : Plane => x 1) h
  exact Prod.ext (Nat.cast_injective h0) (Nat.cast_injective h1)

noncomputable def gridSet (k : ℕ) : Finset Plane :=
  (Finset.range k ×ˢ Finset.range k).image gridPoint

theorem card_gridSet (k : ℕ) : (gridSet k).card = k * k := by
  unfold gridSet
  rw [Finset.card_image_of_injective _ gridPoint_injective,
    Finset.card_product, Finset.card_range]

def gridNormSq (p : ℕ × ℕ) : ℕ :=
  p.1 ^ 2 + p.2 ^ 2

noncomputable def gridNorm (p : ℕ × ℕ) : ℝ :=
  Real.sqrt (gridNormSq p : ℝ)

theorem real_dist_sq_nat (a b : ℕ) :
    dist (a : ℝ) (b : ℝ) ^ 2 = ((Nat.dist a b : ℕ) : ℝ) ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Real.dist_eq, sq_abs, Nat.cast_sub hab]
    ring
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba, Real.dist_eq, sq_abs, Nat.cast_sub hba]

theorem dist_gridPoint_eq_gridNorm (p q : ℕ × ℕ) :
    dist (gridPoint p) (gridPoint q) =
      gridNorm (Nat.dist p.1 q.1, Nat.dist p.2 q.2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  change Real.sqrt (dist (p.1 : ℝ) (q.1 : ℝ) ^ 2 + dist (p.2 : ℝ) (q.2 : ℝ) ^ 2) = _
  rw [real_dist_sq_nat p.1 q.1, real_dist_sq_nat p.2 q.2]
  unfold gridNorm gridNormSq
  push_cast
  rfl

theorem distanceSet_gridSet_subset_image_sqrt (k : ℕ) (hk : 1 ≤ k) :
    Minimizer91.distanceSet (gridSet k) ⊆
      ((range (2 * k ^ 2)).filter (fun m => ∃ x y : ℕ, m = x ^ 2 + y ^ 2)).image
        (fun m : ℕ => Real.sqrt (m : ℝ)) := by
  classical
  intro r hr
  obtain ⟨a, ha, b, hb, _, rfl⟩ :=
    (Erdos91.DistanceErasure.mem_distanceSet (gridSet k) r).mp hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  rw [Finset.mem_range] at hp1 hp2 hq1 hq2
  rw [dist_gridPoint_eq_gridNorm p q]
  unfold gridNorm
  apply Finset.mem_image_of_mem (fun m : ℕ => Real.sqrt (m : ℝ))
  rw [Finset.mem_filter, Finset.mem_range]
  have hdx : Nat.dist p.1 q.1 < k := by unfold Nat.dist; omega
  have hdy : Nat.dist p.2 q.2 < k := by unfold Nat.dist; omega
  refine ⟨?_, Nat.dist p.1 q.1, Nat.dist p.2 q.2, rfl⟩
  unfold gridNormSq
  nlinarith

theorem distinctDistances_gridSet_le_sieve (k : ℕ) (hk : 1 ≤ k) :
    distinctDistances (gridSet k) ≤
      ((range (2 * k ^ 2)).filter (fun m => ∃ x y : ℕ, m = x ^ 2 + y ^ 2)).card := by
  classical
  exact (Finset.card_le_card (distanceSet_gridSet_subset_image_sqrt k hk)).trans
    Finset.card_image_le

theorem exists_grid_sieve_bound_for_C (C : ℕ) :
    ∃ M W : ℕ, 0 < M ∧ 4 * C * W + W < M ∧
      ∀ k : ℕ, 1 ≤ k →
        M * distinctDistances (gridSet k) ≤ (2 * k ^ 2 + M) * W := by
  obtain ⟨M, W, hM, hMW, hbound⟩ := exists_sieve_bound_for_C C
  refine ⟨M, W, hM, hMW, ?_⟩
  intro k hk
  exact (Nat.mul_le_mul_left M (distinctDistances_gridSet_le_sieve k hk)).trans (hbound k hk)

theorem sq_succ_sqrt_le_two_mul {n : ℕ} (hn : 9 ≤ n) :
    (Nat.sqrt n + 1) ^ 2 ≤ 2 * n := by
  have hs3 : 3 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  nlinarith

/-- Integer-multiplier formulation of the Erdős (1946) sublinear upper bound `d(n) = o(n)`. -/
def SublinearMinimalDistances : Prop :=
  ∀ C : ℕ, ∀ᶠ n : ℕ in Filter.atTop, C * minimalDistinctDistances n < n

/-- **Unconditional proof of `SublinearMinimalDistances` (`d(n) = o(n)`) in Lean 4.35:**
for every `C : ℕ`, eventually `C * minimalDistinctDistances n < n`. -/
theorem unconditional_sublinearMinimalDistances : SublinearMinimalDistances := by
  intro C
  obtain ⟨M, W, hM_pos, hMW, hgrid⟩ := exists_grid_sieve_bound_for_C C
  rw [Filter.eventually_atTop]
  refine ⟨max 9 (C * M + 1), ?_⟩
  intro n hn
  have hn9 : 9 ≤ n := le_trans (le_max_left _ _) hn
  have hnCM : C * M + 1 ≤ n := le_trans (le_max_right _ _) hn
  let k := Nat.sqrt n + 1
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hnk2 : n ≤ k * k := by
    have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    dsimp [k]
    omega
  have hd_le : minimalDistinctDistances n ≤ distinctDistances (gridSet k) := by
    calc
      minimalDistinctDistances n ≤ minimalDistinctDistances (k * k) :=
        minimum_monotone hnk2
      _ ≤ distinctDistances (gridSet k) :=
        minimal_le (gridSet k) (k * k) (card_gridSet k)
  have hM_dn : M * minimalDistinctDistances n ≤ (2 * k ^ 2 + M) * W :=
    (Nat.mul_le_mul_left M hd_le).trans (hgrid k hk1)
  have hk2_2n : k ^ 2 ≤ 2 * n := sq_succ_sqrt_le_two_mul hn9
  have hMC_dn : M * (C * minimalDistinctDistances n) < M * n := by
    have hM_4n : M * minimalDistinctDistances n ≤ (4 * n + M) * W :=
      hM_dn.trans (Nat.mul_le_mul_right W (by omega))
    have h1 : C * (M * minimalDistinctDistances n) ≤ C * ((4 * n + M) * W) :=
      Nat.mul_le_mul_left C hM_4n
    have h2 : (C * M) * W ≤ n * W := Nat.mul_le_mul_right W (by omega)
    have h3 : (4 * C * W + W) * n < M * n :=
      Nat.mul_lt_mul_of_pos_right hMW (by omega)
    nlinarith
  exact lt_of_mul_lt_mul_left hMC_dn (by omega)

/-- Equivalence between `SublinearMinimalDistances` and the real-valued limit
`Filter.Tendsto (fun n : ℕ => (minimalDistinctDistances n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0)`. -/
theorem sublinear_iff_tendsto_div_zero :
    SublinearMinimalDistances ↔
      Filter.Tendsto
        (fun n : ℕ => (minimalDistinctDistances n : ℝ) / (n : ℝ))
        Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro hsub ε hε
    obtain ⟨C, hC⟩ := exists_nat_gt (1 / ε)
    have hdiv_pos : 0 < 1 / ε := one_div_pos.mpr hε
    have hC_pos : (0 : ℝ) < (C : ℝ) := lt_trans hdiv_pos hC
    have hεC : 1 < (C : ℝ) * ε := (div_lt_iff₀ hε).mp hC
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hsub C)
    refine ⟨max N0 1, ?_⟩
    intro n hn
    have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlt_nat := hN0 n hn0
    have hlt_real : (C : ℝ) * (minimalDistinctDistances n : ℝ) < (n : ℝ) := by
      exact_mod_cast hlt_nat
    have hnonneg : 0 ≤ (minimalDistinctDistances n : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, div_lt_iff₀ hn_pos]
    have hd_nn : 0 ≤ (minimalDistinctDistances n : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro htend C
    have hε : (0 : ℝ) < 1 / ((C : ℝ) + 1) := by positivity
    obtain ⟨N0, hN0⟩ := htend (1 / ((C : ℝ) + 1)) hε
    rw [Filter.eventually_atTop]
    refine ⟨max N0 1, ?_⟩
    intro n hn
    have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hdist := hN0 n hn0
    have hnonneg : 0 ≤ (minimalDistinctDistances n : ℝ) / (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hn_pos)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, div_lt_iff₀ hn_pos] at hdist
    have hC1_pos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
    have hmul : (C : ℝ) * (minimalDistinctDistances n : ℝ) < (n : ℝ) := by
      have h := (lt_div_iff₀ hC1_pos).mp (by simpa only [one_div_mul_eq_div] using hdist)
      have hd_nn : 0 ≤ (minimalDistinctDistances n : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast hmul

/-- **Unconditional real-valued limit `d(n) / n → 0` as `n → ∞`:**
`Filter.Tendsto (fun n : ℕ => (minimalDistinctDistances n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0)`. -/
theorem unconditional_tendsto_minimalDistinctDistances_div_zero :
    Filter.Tendsto
      (fun n : ℕ => (minimalDistinctDistances n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) :=
  sublinear_iff_tendsto_div_zero.mp unconditional_sublinearMinimalDistances

end Erdos91.SublinearMinimalDistancesProof


/-! ## Unconditional natural-density bound -/

namespace DeletionFamily91
open Finset Minimizer91 PlateauDefinitions91
open EnergyLevels91 (energy centroid energy_level_bound)

theorem family (S B : Finset Plane) (a b p : Plane)
    (hS : S.Nonempty) (hBS : B ⊆ S) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hne : ∀ v ∈ B, v ≠ a ∧ v ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hp : p ∈ S) (hpB : p ∉ B) (hcp : centroid S ≠ p) :
    ∃ F : Finset (Finset Plane),
      (∀ A ∈ F, ∃ v ∈ B, A = S.erase v) ∧
      (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ ∃ f : Plane ≃ᵈ Plane, A.image f = C) ∧
      B.card ≤ 2 * (distanceSet S).card * F.card := by
  classical
  obtain ⟨U, hUB, hinj, himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (B : Set Plane) (B.image (energy S)) (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hy
      exact ⟨v, hv, rfl⟩)
  have hUS : U ⊆ S := fun v hv => hBS (hUB hv)
  have hcard : (U.image S.erase).card = (B.image (energy S)).card := by
    rw [Finset.card_image_of_injOn (S.erase_injOn.mono hUS)]
    rw [← himage, Finset.card_image_of_injOn hinj]
  refine ⟨U.image S.erase, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    exact ⟨v, hUB hv, rfl⟩
  · intro A hA C hC hAC
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hA
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hC
    have hvw : v ≠ w := fun he => hAC (congrArg S.erase he)
    exact DeletionEnergy91.nonsimilar_deletions S a b v w hab ha hb
      (hUS hv) (hUS hw) (hne v (hUB hv)).1 (hne v (hUB hv)).2
      (hne w (hUB hw)).1 (hne w (hUB hw)).2 hdiam
      (fun he => hvw (hinj hv hw he))
  · rw [hcard]
    exact energy_level_bound S B hS hBS p hp hpB hcp

end DeletionFamily91

namespace PlateauFamily91
open Finset Minimizer91 PlateauDefinitions91

theorem optimal_family (n : ℕ) (hn : 3 ≤ n) (S : Finset Plane)
    (hSopt : IsOptimal S (n + 1))
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 1)) :
    ∃ F : Finset (Finset Plane),
      (∀ A ∈ F, A ⊆ S ∧ IsOptimal A n) ∧
      (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ DilationEquivSimilar A C) ∧
      n - 1 ≤ 2 * minimalDistinctDistances n * F.card := by
  classical
  have hScard : S.card = n + 1 := hSopt.1
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, b, hb, hab, hdiam⟩ := exists_diameter_pair S (by omega)
  let B := S \ {a, b}
  have hBS : B ⊆ S := Finset.sdiff_subset
  have hmem (v : Plane) : v ∈ B ↔ v ∈ S ∧ v ≠ a ∧ v ≠ b := by
    simp only [B, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hpair : ({a, b} : Finset Plane) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · exact (Finset.mem_singleton.mp hx) ▸ hb
  have hBcard : B.card = n - 1 := by
    rw [Finset.card_sdiff_of_subset hpair, Finset.card_pair hab, hScard]
    omega
  have hopt (v : Plane) (hv : v ∈ S) : IsOptimal (S.erase v) n := by
    apply MinimumMonotone91.plateau_subset_optimal (S.erase v) S n (n + 1)
      hSopt (Finset.erase_subset _ _) _ hplateau
    rw [Finset.card_erase_of_mem hv, hScard]
    omega
  have hanchor : ∃ p ∈ S, p ∉ B ∧ EnergyLevels91.centroid S ≠ p := by
    by_cases hc : EnergyLevels91.centroid S = a
    · refine ⟨b, hb, by simp [hmem], ?_⟩
      simpa only [hc] using hab
    · exact ⟨a, ha, by simp [hmem], hc⟩
  obtain ⟨p, hp, hpB, hcp⟩ := hanchor
  obtain ⟨F, hdel, hnon, hbound⟩ := DeletionFamily91.family S B a b p
    hSne hBS ha hb hab (fun v hv => (hmem v).mp hv |>.2) hdiam hp hpB hcp
  refine ⟨F, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨v, hv, rfl⟩ := hdel A hA
    exact ⟨Finset.erase_subset _ _, hopt v (hBS hv)⟩
  · intro A hA C hC hAC hs
    exact hnon A hA C hC hAC ((similar_iff_image A C).mp hs)
  · have hd : (distanceSet S).card = minimalDistinctDistances n :=
      hSopt.2.trans hplateau.symm
    simpa only [hBcard, hd] using hbound

end PlateauFamily91


namespace Erdos91.UnconditionalNaturalDensityOne

open Finset Filter Topology Minimizer91 MinimumMonotone91 PlateauDefinitions91
  Erdos91.SublinearMinimalDistancesProof

theorem card_sub_two_le_two_mul_distinctDistances_sq (S : Finset Plane) :
    S.card - 2 ≤ 2 * (distinctDistances S) ^ 2 := by
  classical
  by_cases hcard : S.card < 2
  · omega
  · obtain ⟨c, hc, p, hp, hcp⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    let B := (S.erase c).erase p
    have hpErase : p ∈ S.erase c := Finset.mem_erase.mpr ⟨hcp.symm, hp⟩
    have hBcard : B.card = S.card - 2 := by
      dsimp [B]
      rw [Finset.card_erase_of_mem hpErase, Finset.card_erase_of_mem hc]
      omega
    have hsub_p : B.image (fun v => dist v p) ⊆ distanceSet S := by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hvp, hvc⟩ := Finset.mem_erase.mp hv
      have hvS : v ∈ S := Finset.mem_of_mem_erase hvc
      exact Finset.mem_image.mpr ⟨(v, p), Finset.mem_offDiag.mpr ⟨hvS, hp, hvp⟩, rfl⟩
    have hsub_c : B.image (fun v => dist v c) ⊆ distanceSet S := by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨_, hvc⟩ := Finset.mem_erase.mp hv
      obtain ⟨hvc', hvS⟩ := Finset.mem_erase.mp hvc
      exact Finset.mem_image.mpr ⟨(v, c), Finset.mem_offDiag.mpr ⟨hvS, hc, hvc'⟩, rfl⟩
    have hprod := CircleLevels91.distance_images_product B c p hcp
    have h1 : (B.image (fun v => dist v p)).card ≤ distinctDistances S :=
      Finset.card_le_card hsub_p
    have h2 : (B.image (fun v => dist v c)).card ≤ distinctDistances S :=
      Finset.card_le_card hsub_c
    rw [hBcard] at hprod
    calc
      S.card - 2 ≤ 2 * (B.image (fun v => dist v p)).card *
          (B.image (fun v => dist v c)).card := hprod
      _ ≤ 2 * distinctDistances S * distinctDistances S :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
      _ = 2 * (distinctDistances S) ^ 2 := by ring

theorem minimal_quadratic_lower_bound (n : ℕ) :
    n - 2 ≤ 2 * (minimalDistinctDistances n) ^ 2 := by
  obtain ⟨S, hS⟩ := exists_optimal n
  have h := card_sub_two_le_two_mul_distinctDistances_sq S
  rw [hS.1, hS.2] at h
  exact h

theorem minimalDistinctDistances_unbounded (M : ℕ) :
    ∃ n : ℕ, M < minimalDistinctDistances n := by
  refine ⟨2 * (M + 1) ^ 2 + 2, ?_⟩
  have h := minimal_quadratic_lower_bound (2 * (M + 1) ^ 2 + 2)
  rw [Nat.add_sub_cancel] at h
  by_contra hle
  push Not at hle
  have hsq : (minimalDistinctDistances (2 * (M + 1) ^ 2 + 2)) ^ 2 ≤ M ^ 2 :=
    Nat.pow_le_pow_left hle 2
  have hexp : (M + 1) ^ 2 = M ^ 2 + 2 * M + 1 := by ring
  omega

theorem one_le_minimalDistinctDistances_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    1 ≤ minimalDistinctDistances n := by
  have h := minimal_quadratic_lower_bound n
  by_contra h0
  have hd0 : minimalDistinctDistances n = 0 := by omega
  rw [hd0] at h
  omega

def HasAtLeastKNonsimilarMinimizers (K n : ℕ) : Prop :=
  ∃ F : Finset (Finset Plane),
    F.card = K ∧
    (∀ A ∈ F, IsOptimal A n) ∧
    (∀ A ∈ F, ∀ C ∈ F, A ≠ C → ¬ DilationEquivSimilar A C)

theorem plateau_has_K_minimizers (K n : ℕ) (hn : 3 ≤ n)
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 1))
    (hlow : 2 * (K - 1) * minimalDistinctDistances n < n - 1) :
    HasAtLeastKNonsimilarMinimizers K n := by
  classical
  obtain ⟨S, hSopt⟩ := exists_optimal (n + 1)
  obtain ⟨F', hA, hnon, hprod⟩ := PlateauFamily91.optimal_family n hn S hSopt hplateau
  have hKF : K ≤ F'.card := by
    by_contra hlt
    push Not at hlt
    have hle : F'.card ≤ K - 1 := by omega
    have hmul : 2 * minimalDistinctDistances n * F'.card ≤
        2 * minimalDistinctDistances n * (K - 1) :=
      Nat.mul_le_mul_left _ hle
    have hcomm : 2 * minimalDistinctDistances n * (K - 1) =
        2 * (K - 1) * minimalDistinctDistances n := by ring
    omega
  obtain ⟨F, hFF', hFcard⟩ := Finset.exists_subset_card_eq hKF
  exact ⟨F, hFcard, fun A hAF => (hA A (hFF' hAF)).2,
    fun A hAF C hCF hAC => hnon A (hFF' hAF) C (hFF' hCF) hAC⟩

theorem not_has_K_minimizers_imp_strict_rise (K n : ℕ) (hn : 3 ≤ n)
    (hlow : 2 * (K - 1) * minimalDistinctDistances n < n - 1)
    (hnot : ¬ HasAtLeastKNonsimilarMinimizers K n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    minimum_monotone (by omega)
  rcases eq_or_lt_of_le hle with hflat | hlt
  · exact False.elim (hnot (plateau_has_K_minimizers K n hn hflat hlow))
  · exact hlt

theorem plateau_not_unique_of_two_mul_lt_sub_one (n : ℕ) (hn : 3 ≤ n)
    (hplateau : minimalDistinctDistances n = minimalDistinctDistances (n + 1))
    (hlow : 2 * minimalDistinctDistances n < n - 1) :
    ¬ UniqueMinimizer n := by
  intro huniq
  have hlow2 : 2 * (2 - 1) * minimalDistinctDistances n < n - 1 := by simpa using hlow
  obtain ⟨F, hFcard, hFopt, hFnon⟩ := plateau_has_K_minimizers 2 n hn hplateau hlow2
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  exact hFnon A hA B hB hAB (huniq A B (hFopt A hA) (hFopt B hB))

theorem uniqueMinimizer_imp_strict_rise_of_two_mul_lt_sub_one (n : ℕ) (hn : 3 ≤ n)
    (hlow : 2 * minimalDistinctDistances n < n - 1)
    (huniq : UniqueMinimizer n) :
    minimalDistinctDistances n < minimalDistinctDistances (n + 1) := by
  have hle : minimalDistinctDistances n ≤ minimalDistinctDistances (n + 1) :=
    minimum_monotone (by omega)
  rcases eq_or_lt_of_le hle with hflat | hlt
  · exact False.elim (plateau_not_unique_of_two_mul_lt_sub_one n hn hflat hlow huniq)
  · exact hlt

noncomputable instance : DecidablePred UniqueMinimizer :=
  Classical.decPred _

noncomputable instance (K : ℕ) : DecidablePred (HasAtLeastKNonsimilarMinimizers K) :=
  Classical.decPred _

noncomputable def uniqueMinimizerSet (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter UniqueMinimizer

noncomputable def badMultiplicitySet (K N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => ¬ HasAtLeastKNonsimilarMinimizers K n)

noncomputable def goodMultiplicitySet (K N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (HasAtLeastKNonsimilarMinimizers K)

theorem good_add_badMultiplicitySet_card (K N : ℕ) :
    (goodMultiplicitySet K N).card + (badMultiplicitySet K N).card = N + 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range (N + 1)) (p := HasAtLeastKNonsimilarMinimizers K)
  simpa only [goodMultiplicitySet, badMultiplicitySet, Finset.card_range] using h

theorem badMultiplicitySet_card_le_of_forall (K L N : ℕ) (hL : 3 ≤ L)
    (hlow : ∀ n : ℕ, L ≤ n → 2 * (K - 1) * minimalDistinctDistances n < n - 1) :
    (badMultiplicitySet K N).card ≤ L + minimalDistinctDistances (N + 1) := by
  classical
  let B := badMultiplicitySet K N
  let E1 := B.filter (fun n => n < L)
  let E2 := B.filter (fun n => ¬ n < L)
  have hpart : E1.card + E2.card = B.card :=
    Finset.card_filter_add_card_filter_not (s := B) (p := fun n => n < L)
  have hE1_sub : E1 ⊆ Finset.range L :=
    fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
  have hE1_le : E1.card ≤ L := by
    have h := Finset.card_le_card hE1_sub
    simpa only [Finset.card_range] using h
  have hE2_sub : E2 ⊆ Finset.Icc L N := by
    intro n hn
    obtain ⟨hnB, hge⟩ := Finset.mem_filter.mp hn
    have hn_le : n < N + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hnB).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hE2_le : E2.card ≤ minimalDistinctDistances (N + 1) - minimalDistinctDistances L := by
    apply OneStepCount91.card_le minimalDistinctDistances minimum_monotone E2 L N hE2_sub
    intro n hn
    have hLn : L ≤ n := (Finset.mem_Icc.mp (hE2_sub hn)).1
    have hbad : ¬ HasAtLeastKNonsimilarMinimizers K n :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    exact not_has_K_minimizers_imp_strict_rise K n (by omega) (hlow n hLn) hbad
  change B.card ≤ L + minimalDistinctDistances (N + 1)
  omega

/-- **Unconditional global bound on `badMultiplicitySet K N` for every `K : ℕ`:**
for every `K : ℕ`, there exists `L : ℕ` such that for all `N : ℕ`,
`(badMultiplicitySet K N).card ≤ L + minimalDistinctDistances (N + 1)`. -/
theorem unconditional_exists_badMultiplicitySet_global_bound (K : ℕ) :
    ∃ L : ℕ, ∀ N : ℕ,
      (badMultiplicitySet K N).card ≤ L + minimalDistinctDistances (N + 1) := by
  obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.mp (unconditional_sublinearMinimalDistances (2 * K + 2))
  let L := max L0 3
  refine ⟨L, ?_⟩
  intro N
  apply badMultiplicitySet_card_le_of_forall K L N (by omega)
  intro n hn
  have hn0 : L0 ≤ n := le_trans (le_max_left L0 3) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right L0 3) hn
  have hlt := hL0 n hn0
  have hmul : 2 * (K - 1) * minimalDistinctDistances n +
      2 * minimalDistinctDistances n ≤ (2 * K + 2) * minimalDistinctDistances n := by
    have hle : 2 * (K - 1) + 2 ≤ 2 * K + 2 := by omega
    calc
      2 * (K - 1) * minimalDistinctDistances n + 2 * minimalDistinctDistances n =
          (2 * (K - 1) + 2) * minimalDistinctDistances n := by ring
      _ ≤ (2 * K + 2) * minimalDistinctDistances n :=
        Nat.mul_le_mul_right _ hle
  have hd1 : 1 ≤ minimalDistinctDistances n :=
    one_le_minimalDistinctDistances_of_three_le n hn3
  omega

/-- **Unconditional natural-density-zero bound for `badMultiplicitySet K N`:**
for every `K, M : ℕ`, eventually `M * (badMultiplicitySet K N).card < N + 1`. -/
theorem unconditional_eventually_badMultiplicitySet_card_lt (K M : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, M * (badMultiplicitySet K N).card < N + 1 := by
  obtain ⟨L, hL⟩ := unconditional_exists_badMultiplicitySet_global_bound K
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (unconditional_sublinearMinimalDistances (2 * M))
  rw [Filter.eventually_atTop]
  refine ⟨max N0 (2 * M * L + 1), ?_⟩
  intro N hN
  have hN_ge0 : N0 ≤ N + 1 := by
    have : N0 ≤ N := le_trans (le_max_left _ _) hN
    omega
  have hN_geL : 2 * M * L + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hsmall := hN0 (N + 1) hN_ge0
  have hcard := hL N
  have hmul_card : M * (badMultiplicitySet K N).card ≤
      M * L + M * minimalDistinctDistances (N + 1) := by
    have h := Nat.mul_le_mul_left M hcard
    simpa only [Nat.mul_add] using h
  have h2M : 2 * (M * minimalDistinctDistances (N + 1)) =
      (2 * M) * minimalDistinctDistances (N + 1) := by ring
  have h2ML : 2 * (M * L) = 2 * M * L := by ring
  omega

/-- **Unconditional natural-density-one theorem for `goodMultiplicitySet K N`:**
for every fixed `K : ℕ` and every `M > 0`, eventually
`(M - 1) * (N + 1) < M * (goodMultiplicitySet K N).card`. -/
theorem unconditional_eventually_goodMultiplicitySet_density_one (K M : ℕ) (hM : 0 < M) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (M - 1) * (N + 1) < M * (goodMultiplicitySet K N).card := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (unconditional_eventually_badMultiplicitySet_card_lt K M)
  rw [Filter.eventually_atTop]
  refine ⟨N1, ?_⟩
  intro N hN
  have hbad := hN1 N hN
  have hsum := good_add_badMultiplicitySet_card K N
  have hM_sum : M * (goodMultiplicitySet K N).card +
      M * (badMultiplicitySet K N).card = M * (N + 1) := by
    rw [← Nat.mul_add, hsum]
  have hM_split : (M - 1) * (N + 1) + (N + 1) = M * (N + 1) := by
    have h : (M - 1) + 1 = M := by omega
    calc
      (M - 1) * (N + 1) + (N + 1) = ((M - 1) + 1) * (N + 1) := by ring
      _ = M * (N + 1) := by rw [h]
  omega

/-- **Unconditional real-valued natural-density-zero limit for `badMultiplicitySet K N`:**
for every `K : ℕ`, `((badMultiplicitySet K N).card : ℝ) / (N + 1) → 0` as `N → ∞`. -/
theorem unconditional_tendsto_badMultiplicitySet_density_zero (K : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ((badMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hdiv_pos : 0 < 1 / ε := one_div_pos.mpr hε
  have hM_pos : (0 : ℝ) < (M : ℝ) := lt_trans hdiv_pos hM
  have hεM : 1 < (M : ℝ) * ε := (div_lt_iff₀ hε).mp hM
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (unconditional_eventually_badMultiplicitySet_card_lt K M)
  refine ⟨N0, ?_⟩
  intro N hN
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hlt_nat := hN0 N hN
  have hlt_real : (M : ℝ) * ((badMultiplicitySet K N).card : ℝ) < (N : ℝ) + 1 := by
    exact_mod_cast hlt_nat
  have hnonneg : 0 ≤ ((badMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hN1_pos)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, div_lt_iff₀ hN1_pos]
  have hcard_nn : 0 ≤ ((badMultiplicitySet K N).card : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **Unconditional real-valued natural-density-one limit for `goodMultiplicitySet K N`:**
for every `K : ℕ`, `((goodMultiplicitySet K N).card : ℝ) / (N + 1) → 1` as `N → ∞`. -/
theorem unconditional_tendsto_goodMultiplicitySet_density_one (K : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ((goodMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1))
      Filter.atTop (nhds 1) := by
  have hbad := Metric.tendsto_atTop.mp (unconditional_tendsto_badMultiplicitySet_density_zero K)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := hbad ε hε
  refine ⟨N0, ?_⟩
  intro N hN
  have hsum_nat := good_add_badMultiplicitySet_card K N
  have hsum_real : ((goodMultiplicitySet K N).card : ℝ) +
      ((badMultiplicitySet K N).card : ℝ) = (N : ℝ) + 1 := by
    exact_mod_cast hsum_nat
  have hN1_ne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hdist_eq :
      dist (((goodMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1)) 1 =
        dist (((badMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1)) 0 := by
    have hsub_eq :
        ((goodMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1) - 1 =
          -(((badMultiplicitySet K N).card : ℝ) / ((N : ℝ) + 1)) := by
      have hg : ((goodMultiplicitySet K N).card : ℝ) =
          ((N : ℝ) + 1) - ((badMultiplicitySet K N).card : ℝ) := by linarith
      rw [hg, sub_div, div_self hN1_ne]
      ring
    rw [Real.dist_eq, Real.dist_eq, sub_zero, hsub_eq, abs_neg]
  rw [hdist_eq]
  exact hN0 N hN

theorem uniqueMinimizerSet_subset_badMultiplicitySet_two (N : ℕ) :
    uniqueMinimizerSet N ⊆ badMultiplicitySet 2 N := by
  intro n hn
  obtain ⟨hn_range, huniq⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn_range, ?_⟩
  rintro ⟨F, hFcard, hFopt, hFnon⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  exact hFnon A hA B hB hAB (huniq A B (hFopt A hA) (hFopt B hB))

/-- **Unconditional natural-density-zero bound for `uniqueMinimizerSet N`:**
for every `M : ℕ`, eventually `M * (uniqueMinimizerSet N).card < N + 1`. -/
theorem unconditional_eventually_uniqueMinimizerSet_card_lt (M : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, M * (uniqueMinimizerSet N).card < N + 1 := by
  filter_upwards [unconditional_eventually_badMultiplicitySet_card_lt 2 M] with N hN
  have hle := Finset.card_le_card (uniqueMinimizerSet_subset_badMultiplicitySet_two N)
  exact (Nat.mul_le_mul_left M hle).trans_lt hN

/-- **Unconditional real-valued natural-density-zero limit for `uniqueMinimizerSet N`:**
`((uniqueMinimizerSet N).card : ℝ) / (N + 1) → 0` as `N → ∞`. -/
theorem unconditional_tendsto_uniqueMinimizerSet_density_zero :
    Filter.Tendsto
      (fun N : ℕ => ((uniqueMinimizerSet N).card : ℝ) / ((N : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hbad := Metric.tendsto_atTop.mp (unconditional_tendsto_badMultiplicitySet_density_zero 2)
  obtain ⟨N0, hN0⟩ := hbad ε hε
  refine ⟨N0, ?_⟩
  intro N hN
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle_nat := Finset.card_le_card (uniqueMinimizerSet_subset_badMultiplicitySet_two N)
  have hle_real : ((uniqueMinimizerSet N).card : ℝ) ≤ ((badMultiplicitySet 2 N).card : ℝ) := by
    exact_mod_cast hle_nat
  have hnn1 : 0 ≤ ((uniqueMinimizerSet N).card : ℝ) / ((N : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) hN1_pos.le
  have hnn2 : 0 ≤ ((badMultiplicitySet 2 N).card : ℝ) / ((N : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) hN1_pos.le
  have hdist := hN0 N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn2] at hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn1]
  exact (div_le_div_of_nonneg_right hle_real hN1_pos.le).trans_lt hdist

theorem exists_k_flat_strict_rise_seq (k : ℕ) (hk : 1 ≤ k)
    (f : ℕ → ℕ) (hf : Monotone f)
    (hunbounded : ∀ M : ℕ, ∃ n : ℕ, M < f n)
    (hsubk : ∀ K : ℕ, ∃ j : ℕ, f (K + k * j) < j) (N : ℕ) :
    ∃ n : ℕ, max N k ≤ n ∧ f (n - k) = f n ∧ f n < f (n + 1) := by
  classical
  by_contra hnot
  let K := max N k
  have hkk : k ≤ K := le_max_right N k
  have hnext : ∀ a : ℕ, K ≤ a → f (a - k) = f a → f (a + 1) ≤ f a := by
    intro a ha hflat
    by_contra hbad
    apply hnot
    refine ⟨a, ha, hflat, ?_⟩
    omega
  have hNoFlat : ∀ a : ℕ, K ≤ a → f (a - k) ≠ f a := by
    intro a ha heq
    have htail : ∀ j : ℕ, f (a + j) = f a := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hwindow : f ((a + j) - k) = f (a + j) := by
          apply le_antisymm (hf (Nat.sub_le _ _))
          rw [ih, ← heq]
          exact hf (by omega)
        have hstep : f (a + j + 1) ≤ f (a + j) :=
          hnext (a + j) (by omega) hwindow
        have hsame : f (a + j + 1) = f a := by
          have hs : f (a + j + 1) = f (a + j) :=
            le_antisymm hstep (hf (by omega))
          exact hs.trans ih
        simpa only [Nat.add_assoc] using hsame
    obtain ⟨b, hb⟩ := hunbounded (f a)
    by_cases hba : b ≤ a
    · exact (not_lt_of_ge (hf hba)) hb
    · have hindex : a + (b - a) = b := by omega
      have hbEq : f b = f a := by
        simpa only [hindex] using htail (b - a)
      omega
  have hstepk : ∀ n : ℕ, K ≤ n → f n < f (n + k) := by
    intro n hn
    have hm : f n ≤ f (n + k) := hf (by omega)
    have hne := hNoFlat (n + k) (by omega)
    have hindex : (n + k) - k = n := by omega
    rw [hindex] at hne
    omega
  have hgrowth : ∀ j : ℕ, j ≤ f (K + k * j) := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hstep := hstepk (K + k * j) (by omega)
      have hindex : K + k * (j + 1) = (K + k * j) + k := by ring
      rw [hindex]
      omega
  obtain ⟨j, hj⟩ := hsubk K
  have hlo := hgrowth j
  omega

theorem unconditional_exists_minimalDistinctDistances_lt_k_shift
    (k : ℕ) (hk : 1 ≤ k) (K : ℕ) :
    ∃ j : ℕ, minimalDistinctDistances (K + k * j) < j := by
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (unconditional_sublinearMinimalDistances (k + 1))
  let j := K + N0 + 1
  refine ⟨j, ?_⟩
  have hkj : j ≤ k * j := by
    have h := Nat.mul_le_mul_right j hk
    simpa using h
  have hge : N0 ≤ K + k * j := by omega
  have hlt := hN0 (K + k * j) hge
  have hmul : k * minimalDistinctDistances (K + k * j) +
      minimalDistinctDistances (K + k * j) =
      (k + 1) * minimalDistinctDistances (K + k * j) := by ring
  by_contra hbad
  push Not at hbad
  have hkmul : k * j ≤ k * minimalDistinctDistances (K + k * j) :=
    Nat.mul_le_mul_left k hbad
  omega

/-- **Unconditional cofinal existence of `k`-flat strict rises for every `k ≥ 1`:**
for every `k ≥ 1` and `N : ℕ`, there exists `n ≥ max N k` with
`d(n - k) = d(n) < d(n + 1)`. -/
theorem unconditional_exists_k_flat_strict_rise (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ∃ n : ℕ, max N k ≤ n ∧
      minimalDistinctDistances (n - k) = minimalDistinctDistances n ∧
      minimalDistinctDistances n < minimalDistinctDistances (n + 1) :=
  exists_k_flat_strict_rise_seq k hk minimalDistinctDistances
    minimum_monotone
    minimalDistinctDistances_unbounded
    (unconditional_exists_minimalDistinctDistances_lt_k_shift k hk) N


theorem flat_sdiff_distanceSet (A U : Finset Plane) (n k : ℕ)
    (hA : IsOptimal A n) (hUA : U ⊆ A) (hUcard : U.card = k)
    (hflat : minimalDistinctDistances (n - k) = minimalDistinctDistances n) :
    Erdos91.DistanceErasure.distanceSet (A \ U) =
      Erdos91.DistanceErasure.distanceSet A := by
  classical
  have hcard : (A \ U).card = n - k := by
    rw [Finset.card_sdiff_of_subset hUA, hA.1, hUcard]
  have hsub : Erdos91.DistanceErasure.distanceSet (A \ U) ⊆
      Erdos91.DistanceErasure.distanceSet A := by
    change (A \ U).offDiag.image (fun p => dist p.1 p.2) ⊆
      A.offDiag.image (fun p => dist p.1 p.2)
    exact Finset.image_subset_image (Finset.offDiag_mono Finset.sdiff_subset)
  have hmin := minimal_le (A \ U) (n - k) hcard
  rw [hflat] at hmin
  apply Finset.eq_of_subset_of_card_le hsub
  change distinctDistances A ≤ distinctDistances (A \ U)
  rw [hA.2]
  exact hmin

theorem flat_sdiff_optimal (A U : Finset Plane) (n k : ℕ)
    (hA : IsOptimal A n) (hUA : U ⊆ A) (hUcard : U.card = k)
    (hflat : minimalDistinctDistances (n - k) = minimalDistinctDistances n) :
    IsOptimal (A \ U) (n - k) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hUA, hA.1, hUcard]
  · change (Erdos91.DistanceErasure.distanceSet (A \ U)).card =
      minimalDistinctDistances (n - k)
    rw [flat_sdiff_distanceSet A U n k hA hUA hUcard hflat]
    change distinctDistances A = minimalDistinctDistances (n - k)
    rw [hA.2, hflat]

/-- **Unconditional cofinal `k`-flat multi-site core theorem for every `k ≥ 1`:**
for every cluster size `k ≥ 1` and `N : ℕ`, there exist arbitrarily late `k`-flat
strict rises `d(n - k) = d(n) < d(n + 1)` where every optimal `n`-point configuration
`A` and every `k`-point subset `U ⊆ A` supplies an optimal `(n - k)`-point core
`A \ U` preserving the full distance set `distanceSet (A \ U) = distanceSet A`. -/
theorem unconditional_cofinal_k_flat_multisite_core (k : ℕ) (hk : 1 ≤ k) (N : ℕ) :
    ∃ n : ℕ, max N k ≤ n ∧
      minimalDistinctDistances (n - k) = minimalDistinctDistances n ∧
      minimalDistinctDistances n < minimalDistinctDistances (n + 1) ∧
      (∀ A U : Finset Plane, IsOptimal A n → U ⊆ A → U.card = k →
        IsOptimal (A \ U) (n - k) ∧
          Erdos91.DistanceErasure.distanceSet (A \ U) =
            Erdos91.DistanceErasure.distanceSet A) := by
  obtain ⟨n, hn, hflat, hgap⟩ := unconditional_exists_k_flat_strict_rise k hk N
  refine ⟨n, hn, hflat, hgap, ?_⟩
  intro A U hA hUA hUcard
  exact ⟨flat_sdiff_optimal A U n k hA hUA hUcard hflat,
    flat_sdiff_distanceSet A U n k hA hUA hUcard hflat⟩

end Erdos91.UnconditionalNaturalDensityOne



/-! ## Distance-complete core pair-deletion families -/

/-!
# Universal Distance-Complete Core Pair-Deletion Invariance, Similarity Invariants, and Triangular Lattice Patch Families for `n ≥ 10` (Erdős Problem #91)
-/

namespace Erdos91.DistanceCompleteCoreDeletionInvariance
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91

/-- A subset `C ⊆ P` is a **distance-complete core** of `P` if `C ⊆ P` and `C` already
realizes the full distance set of `P` (`distanceSet C = distanceSet P`). -/
def IsDistanceCompleteCore (C P : Finset Plane) : Prop :=
  C ⊆ P ∧ Erdos91.DistanceErasure.distanceSet C = Erdos91.DistanceErasure.distanceSet P

/-- Monotonicity of `distanceSet` with respect to subset inclusion. -/
theorem distanceSet_mono {A B : Finset Plane} (h : A ⊆ B) :
    Erdos91.DistanceErasure.distanceSet A ⊆ Erdos91.DistanceErasure.distanceSet B := by
  change A.offDiag.image (fun p => dist p.1 p.2) ⊆ B.offDiag.image (fun p => dist p.1 p.2)
  exact Finset.image_subset_image (Finset.offDiag_mono h)

/-- Characterization of `IsDistanceCompleteCore C P` via `C ⊆ P` and `distanceSet P ⊆ distanceSet C`. -/
theorem isDistanceCompleteCore_iff_subset (C P : Finset Plane) :
    IsDistanceCompleteCore C P ↔
      C ⊆ P ∧ Erdos91.DistanceErasure.distanceSet P ⊆ Erdos91.DistanceErasure.distanceSet C := by
  unfold IsDistanceCompleteCore
  constructor
  · rintro ⟨hCP, heq⟩
    exact ⟨hCP, heq.symm.subset⟩
  · rintro ⟨hCP, hsub⟩
    exact ⟨hCP, Finset.Subset.antisymm (distanceSet_mono hCP) hsub⟩

/-- **Universal Sandwich Distance-Set Invariance (`∀ C A P`):**
any intermediate configuration `C ⊆ A ⊆ P` between a distance-complete core `C` and `P`
has the exact distance set and distinct-distance count of `P`. -/
theorem distanceSet_eq_of_subset_between (C A P : Finset Plane)
    (hC : IsDistanceCompleteCore C P) (hCA : C ⊆ A) (hAP : A ⊆ P) :
    Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances A = distinctDistances P := by
  have h1 : Erdos91.DistanceErasure.distanceSet C ⊆ Erdos91.DistanceErasure.distanceSet A :=
    distanceSet_mono hCA
  have h2 : Erdos91.DistanceErasure.distanceSet A ⊆ Erdos91.DistanceErasure.distanceSet P :=
    distanceSet_mono hAP
  rw [hC.2] at h1
  have heq := Finset.Subset.antisymm h2 h1
  refine ⟨heq, ?_⟩
  change (Erdos91.DistanceErasure.distanceSet A).card =
    (Erdos91.DistanceErasure.distanceSet P).card
  rw [heq]

/-- **Universal `k`-Deletion Distance-Set Invariance (`∀ C P D`):**
if `C` is a distance-complete core of `P`, then for every deletion subset `D` disjoint from `C`,
`distanceSet (P \ D) = distanceSet P` and `distinctDistances (P \ D) = distinctDistances P`. -/
theorem distanceSet_sdiff_eq_of_isDistanceCompleteCore (C P D : Finset Plane)
    (hC : IsDistanceCompleteCore C P) (hDC : Disjoint D C) :
    Erdos91.DistanceErasure.distanceSet (P \ D) = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances (P \ D) = distinctDistances P := by
  apply distanceSet_eq_of_subset_between C (P \ D) P hC _ Finset.sdiff_subset
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨hC.1 hx, Finset.disjoint_left.mp hDC.symm hx⟩

/-- **Universal Single-Deletion Distance-Set Invariance (`∀ C P u`):**
deleting any vertex `u ∉ C` outside a distance-complete core `C` preserves `distanceSet P`. -/
theorem distanceSet_erase_eq_of_isDistanceCompleteCore (C P : Finset Plane) (u : Plane)
    (hC : IsDistanceCompleteCore C P) (huC : u ∉ C) :
    Erdos91.DistanceErasure.distanceSet (P.erase u) = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances (P.erase u) = distinctDistances P := by
  apply distanceSet_eq_of_subset_between C (P.erase u) P hC _ (Finset.erase_subset u P)
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun h => huC (h ▸ hx), hC.1 hx⟩

/-- **Universal Pair-Deletion Distance-Set Invariance (`∀ C P u v`):**
deleting any pair of vertices `u, v ∉ C` outside a distance-complete core `C` preserves
both `distanceSet P` and `distinctDistances P`. -/
theorem distanceSet_pair_erase_eq_of_isDistanceCompleteCore (C P : Finset Plane) (u v : Plane)
    (hC : IsDistanceCompleteCore C P) (huC : u ∉ C) (hvC : v ∉ C) :
    Erdos91.DistanceErasure.distanceSet ((P.erase u).erase v) =
        Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances ((P.erase u).erase v) = distinctDistances P := by
  apply distanceSet_eq_of_subset_between C ((P.erase u).erase v) P hC _
    ((Finset.erase_subset v (P.erase u)).trans (Finset.erase_subset u P))
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun h => hvC (h ▸ hx),
    Finset.mem_erase.mpr ⟨fun h => huC (h ▸ hx), hC.1 hx⟩⟩

/-- **Universal `k`-Deletion Optimality from a Distance-Complete Core (`∀ C P D k`):**
if `C` is a distance-complete core of `P` and `distinctDistances P ≤ d(P.card - k)`,
then for every `D ⊆ P` disjoint from `C` with `D.card = k`, `P \ D` is globally optimal
for `P.card - k` (`IsOptimal (P \ D) (P.card - k)`). -/
theorem isOptimal_sdiff_of_isDistanceCompleteCore (C P D : Finset Plane) (k : ℕ)
    (hC : IsDistanceCompleteCore C P) (hDP : D ⊆ P) (hDC : Disjoint D C)
    (hDcard : D.card = k)
    (hmin : distinctDistances P ≤ minimalDistinctDistances (P.card - k)) :
    IsOptimal (P \ D) (P.card - k) ∧
      Erdos91.DistanceErasure.distanceSet (P \ D) = Erdos91.DistanceErasure.distanceSet P := by
  obtain ⟨hDS, hdist⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore C P D hC hDC
  have hcard : (P \ D).card = P.card - k := by
    rw [Finset.card_sdiff_of_subset hDP, hDcard]
  have hlo := minimal_le (P \ D) (P.card - k) hcard
  exact ⟨⟨hcard, by omega⟩, hDS⟩

/-- **Universal Pair-Deletion Optimality from a Distance-Complete Core (`∀ C P u v`):**
if `C` is a distance-complete core of `P` and `distinctDistances P ≤ d(P.card - 2)`,
then for every distinct pair `u, v ∈ P` with `u, v ∉ C`, `(P.erase u).erase v` is
globally optimal for `P.card - 2` (`IsOptimal ((P.erase u).erase v) (P.card - 2)`). -/
theorem isOptimal_pair_erase_of_isDistanceCompleteCore (C P : Finset Plane) (u v : Plane)
    (hC : IsDistanceCompleteCore C P) (huP : u ∈ P) (hvP : v ∈ P) (huv : u ≠ v)
    (huC : u ∉ C) (hvC : v ∉ C)
    (hmin : distinctDistances P ≤ minimalDistinctDistances (P.card - 2)) :
    IsOptimal ((P.erase u).erase v) (P.card - 2) ∧
      Erdos91.DistanceErasure.distanceSet ((P.erase u).erase v) =
        Erdos91.DistanceErasure.distanceSet P := by
  obtain ⟨hDS, hdist⟩ := distanceSet_pair_erase_eq_of_isDistanceCompleteCore C P u v hC huC hvC
  have hv_er : v ∈ P.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvP⟩
  have hcard : ((P.erase u).erase v).card = P.card - 2 := by
    rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem huP]
    omega
  have hlo := minimal_le ((P.erase u).erase v) (P.card - 2) hcard
  exact ⟨⟨hcard, by omega⟩, hDS⟩

end Erdos91.DistanceCompleteCoreDeletionInvariance


/-! ## Suite 2: Universal Distance-Multiplicity, Maximum-Distance Multiplicity, and `pairDelScore` Invariants (`∀ A B P C a b u₁ v₁ u₂ v₂ F K`) -/

namespace Erdos91.PairDeletionInvariantsAndMultiplicity
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.ExactGridEnergyAndDeletionFamilies
  Erdos91.ThreeUniqueMinimizer
  Erdos91.UnconditionalNaturalDensityOne
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Ordered off-diagonal pairs in `A` realizing distance `r`. -/
noncomputable def distPairFiber (A : Finset Plane) (r : ℝ) : Finset (Plane × Plane) :=
  A.offDiag.filter (fun p => dist p.1 p.2 = r)

/-- Ordered-pair multiplicity `distPairCount A r` of distance `r` in `A`. -/
noncomputable def distPairCount (A : Finset Plane) (r : ℝ) : ℕ :=
  (distPairFiber A r).card

/-- Under any planar similarity `f : Plane ≃ᵈ Plane`, the fiber at scaled distance
`(Dilation.ratio f) * r` is the image of `distPairFiber A r` under `(x, y) ↦ (f x, f y)`. -/
theorem distPairFiber_image_dilationEquiv (A : Finset Plane) (f : Plane ≃ᵈ Plane) (r : ℝ) :
    distPairFiber (A.image f) ((Dilation.ratio f : ℝ) * r) =
      (distPairFiber A r).image (fun p => (f p.1, f p.2)) := by
  unfold distPairFiber
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_image, Prod.ext_iff]
  constructor
  · rintro ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hne⟩, hd⟩
    have hab : a ≠ b := fun h => hne (congrArg f h)
    rw [Dilation.dist_eq] at hd
    have hr_ne : (Dilation.ratio f : ℝ) ≠ 0 := ne_of_gt (Dilation.ratio_pos f)
    have hdr : dist a b = r := mul_left_cancel₀ hr_ne hd
    exact ⟨(a, b), ⟨⟨ha, hb, hab⟩, hdr⟩, rfl, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb, hab⟩, hdr⟩, rfl, rfl⟩
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, f.injective.ne hab⟩, ?_⟩
    rw [Dilation.dist_eq, hdr]

/-- **Universal Distance-Multiplicity Scaling Law (`∀ A f r`):**
for any `A`, `f : Plane ≃ᵈ Plane`, and `r : ℝ`,
`distPairCount (A.image f) ((Dilation.ratio f : ℝ) * r) = distPairCount A r`. -/
theorem distPairCount_image_dilationEquiv (A : Finset Plane) (f : Plane ≃ᵈ Plane) (r : ℝ) :
    distPairCount (A.image f) ((Dilation.ratio f : ℝ) * r) = distPairCount A r := by
  unfold distPairCount
  rw [distPairFiber_image_dilationEquiv]
  apply Finset.card_image_of_injective
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨f.injective h.1, f.injective h.2⟩

/-- **Universal Shared-Diameter Distance-Multiplicity Invariance (`∀ A B f a b r`):**
if `A.image f = B` and `(a, b)` is a shared diameter pair of `A` and `B`, then every
distance `r : ℝ` has identical multiplicity in `A` and `B` (`distPairCount A r = distPairCount B r`). -/
theorem distPairCount_eq_of_shared_diameter (A B : Finset Plane) (f : Plane ≃ᵈ Plane)
    (himage : A.image f = B) (a b : Plane) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A) (haB : a ∈ B) (hbB : b ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a b)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a b) (r : ℝ) :
    distPairCount A r = distPairCount B r := by
  have hr := SimilarityEnergy91.ratio_one_of_shared_diameter A B f himage a b hab
    haA hbA haB hbB hA hB
  have hc := distPairCount_image_dilationEquiv A f r
  rw [himage, hr, one_mul] at hc
  exact hc.symm

/-- **Universal Shared-Diameter Distance-Multiplicity Nonsimilarity Criterion (`∀ A B a b r`):**
if `A` and `B` share a diameter pair `(a, b)` and `distPairCount A r ≠ distPairCount B r`
for some `r : ℝ`, then `¬ DilationEquivSimilar A B`. -/
theorem not_similar_of_shared_diameter_distPairCount_ne
    (A B : Finset Plane) (a b : Plane) (r : ℝ) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A) (haB : a ∈ B) (hbB : b ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a b)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a b)
    (hne : distPairCount A r ≠ distPairCount B r) :
    ¬ DilationEquivSimilar A B := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image A B).mp hsim
  exact hne (distPairCount_eq_of_shared_diameter A B f hf a b hab haA hbA haB hbB hA hB r)

/-- **Universal Maximum-Distance (Diameter) Multiplicity Similarity Invariance (`∀ A B`):**
for any two similar configurations `A, B` (`DilationEquivSimilar A B`) with diameter
pairs `(a₁, b₁)` in `A` and `(a₂, b₂)` in `B` (not necessarily shared), the diameter
multiplicities coincide: `distPairCount A (dist a₁ b₁) = distPairCount B (dist a₂ b₂)`. -/
theorem maxDistPairCount_eq_of_similar (A B : Finset Plane) (a₁ b₁ a₂ b₂ : Plane)
    (hsim : DilationEquivSimilar A B)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ B) (hb₂ : b₂ ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a₁ b₁)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a₂ b₂) :
    distPairCount A (dist a₁ b₁) = distPairCount B (dist a₂ b₂) := by
  obtain ⟨f, hf⟩ := (similar_iff_image A B).mp hsim
  have hfa₁ : f a₁ ∈ B := hf ▸ Finset.mem_image_of_mem f ha₁
  have hfb₁ : f b₁ ∈ B := hf ▸ Finset.mem_image_of_mem f hb₁
  have hle1 : (Dilation.ratio f : ℝ) * dist a₁ b₁ ≤ dist a₂ b₂ := by
    have h := hB (f a₁) hfa₁ (f b₁) hfb₁
    rwa [Dilation.dist_eq] at h
  have ha₂_img : a₂ ∈ A.image f := hf ▸ ha₂
  have hb₂_img : b₂ ∈ A.image f := hf ▸ hb₂
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha₂_img
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb₂_img
  have hratio_nonneg : 0 ≤ (Dilation.ratio f : ℝ) := NNReal.coe_nonneg _
  have hle2 : dist (f x) (f y) ≤ (Dilation.ratio f : ℝ) * dist a₁ b₁ := by
    rw [Dilation.dist_eq]
    exact mul_le_mul_of_nonneg_left (hA x hx y hy) hratio_nonneg
  have hd_eq : (Dilation.ratio f : ℝ) * dist a₁ b₁ = dist (f x) (f y) :=
    le_antisymm hle1 hle2
  have hc := distPairCount_image_dilationEquiv A f (dist a₁ b₁)
  rw [hf, hd_eq] at hc
  exact hc.symm

/-- **Universal Diameter-Multiplicity Nonsimilarity Criterion (`∀ A B`):**
if `(a₁, b₁)` is a diameter pair of `A`, `(a₂, b₂)` is a diameter pair of `B`, and
`distPairCount A (dist a₁ b₁) ≠ distPairCount B (dist a₂ b₂)`, then `¬ DilationEquivSimilar A B`. -/
theorem not_similar_of_maxDistPairCount_ne (A B : Finset Plane) (a₁ b₁ a₂ b₂ : Plane)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) (ha₂ : a₂ ∈ B) (hb₂ : b₂ ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ dist a₁ b₁)
    (hB : ∀ x ∈ B, ∀ y ∈ B, dist x y ≤ dist a₂ b₂)
    (hne : distPairCount A (dist a₁ b₁) ≠ distPairCount B (dist a₂ b₂)) :
    ¬ DilationEquivSimilar A B :=
  fun hsim => hne (maxDistPairCount_eq_of_similar A B a₁ b₁ a₂ b₂ hsim ha₁ hb₁ ha₂ hb₂ hA hB)

/-- Ambient pair-deletion score `pairDelScore P u v = energy P u + energy P v - dist u v ^ 2`. -/
noncomputable def pairDelScore (P : Finset Plane) (u v : Plane) : ℝ :=
  energy P u + energy P v - dist u v ^ 2

/-- Deleting `u ∈ P` reduces `energy P v` by `dist u v ^ 2`. -/
theorem energy_erase_eq_sub (P : Finset Plane) {u : Plane} (hu : u ∈ P) (v : Plane) :
    energy (P.erase u) v = energy P v - dist u v ^ 2 := by
  unfold energy
  rw [Finset.sum_erase_eq_sub hu, dist_comm]

/-- **Universal Pair-Deletion Pair-Energy Identity (`∀ P u v`):**
for any distinct `u, v ∈ P`, `pairEnergy ((P.erase u).erase v) = pairEnergy P - 2 * pairDelScore P u v`. -/
theorem pairEnergy_pair_erase_eq (P : Finset Plane) {u v : Plane}
    (hu : u ∈ P) (hv : v ∈ P) (huv : u ≠ v) :
    pairEnergy ((P.erase u).erase v) = pairEnergy P - 2 * pairDelScore P u v := by
  have hv_er : v ∈ P.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have h1 := DeletionEnergy91.deletion_identity P u hu
  have h2 := DeletionEnergy91.deletion_identity (P.erase u) v hv_er
  have h3 := energy_erase_eq_sub P hu v
  unfold pairDelScore
  linarith

/-- **Universal Pair-Deletion Pair-Energy Difference Identity (`∀ P u₁ v₁ u₂ v₂`):**
the pair-energy difference between two pair-deletions of `P` equals
`2 * (pairDelScore P u₂ v₂ - pairDelScore P u₁ v₁)`. -/
theorem pairEnergy_pair_erase_sub_eq (P : Finset Plane) {u₁ v₁ u₂ v₂ : Plane}
    (hu₁ : u₁ ∈ P) (hv₁ : v₁ ∈ P) (huv₁ : u₁ ≠ v₁)
    (hu₂ : u₂ ∈ P) (hv₂ : v₂ ∈ P) (huv₂ : u₂ ≠ v₂) :
    pairEnergy ((P.erase u₁).erase v₁) - pairEnergy ((P.erase u₂).erase v₂) =
      2 * (pairDelScore P u₂ v₂ - pairDelScore P u₁ v₁) := by
  rw [pairEnergy_pair_erase_eq P hu₁ hv₁ huv₁, pairEnergy_pair_erase_eq P hu₂ hv₂ huv₂]
  ring

/-- **Universal Shared-Diameter Pair-Deletion Nonsimilarity Criterion (`∀ P a b u₁ v₁ u₂ v₂`):**
if `(a, b)` is a diameter pair of `P` and `{u₁, v₁}, {u₂, v₂} ⊆ P \ {a, b}` are two pairs
with `pairDelScore P u₁ v₁ ≠ pairDelScore P u₂ v₂`, then `(P.erase u₁).erase v₁` and
`(P.erase u₂).erase v₂` are nonsimilar under all full-plane similarities. -/
theorem nonsimilar_pair_erase_of_pairDelScore_ne
    (P : Finset Plane) (a b u₁ v₁ u₂ v₂ : Plane) (hab : a ≠ b)
    (ha : a ∈ P) (hb : b ∈ P)
    (hu₁ : u₁ ∈ P) (hv₁ : v₁ ∈ P) (huv₁ : u₁ ≠ v₁)
    (hu₂ : u₂ ∈ P) (hv₂ : v₂ ∈ P) (huv₂ : u₂ ≠ v₂)
    (h₁a : u₁ ≠ a ∧ v₁ ≠ a) (h₁b : u₁ ≠ b ∧ v₁ ≠ b)
    (h₂a : u₂ ≠ a ∧ v₂ ≠ a) (h₂b : u₂ ≠ b ∧ v₂ ≠ b)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist a b)
    (hne : pairDelScore P u₁ v₁ ≠ pairDelScore P u₂ v₂) :
    ¬ DilationEquivSimilar ((P.erase u₁).erase v₁) ((P.erase u₂).erase v₂) := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image _ _).mp hsim
  let A₁ := (P.erase u₁).erase v₁
  let A₂ := (P.erase u₂).erase v₂
  have ha₁ : a ∈ A₁ := Finset.mem_erase.mpr ⟨h₁a.2.symm, Finset.mem_erase.mpr ⟨h₁a.1.symm, ha⟩⟩
  have hb₁ : b ∈ A₁ := Finset.mem_erase.mpr ⟨h₁b.2.symm, Finset.mem_erase.mpr ⟨h₁b.1.symm, hb⟩⟩
  have ha₂ : a ∈ A₂ := Finset.mem_erase.mpr ⟨h₂a.2.symm, Finset.mem_erase.mpr ⟨h₂a.1.symm, ha⟩⟩
  have hb₂ : b ∈ A₂ := Finset.mem_erase.mpr ⟨h₂b.2.symm, Finset.mem_erase.mpr ⟨h₂b.1.symm, hb⟩⟩
  have hsub₁ : A₁ ⊆ P := (Finset.erase_subset v₁ (P.erase u₁)).trans (Finset.erase_subset u₁ P)
  have hsub₂ : A₂ ⊆ P := (Finset.erase_subset v₂ (P.erase u₂)).trans (Finset.erase_subset u₂ P)
  have hpe := SimilarityEnergy91.pairEnergy_eq_of_shared_diameter A₁ A₂ f hf a b hab
    ha₁ hb₁ ha₂ hb₂
    (fun x hx y hy => hdiam x (hsub₁ hx) y (hsub₁ hy))
    (fun x hx y hy => hdiam x (hsub₂ hx) y (hsub₂ hy))
  have hdiff := pairEnergy_pair_erase_sub_eq P hu₁ hv₁ huv₁ hu₂ hv₂ huv₂
  change pairEnergy A₁ - pairEnergy A₂ = _ at hdiff
  rw [hpe, sub_self] at hdiff
  apply hne
  linarith

/-- **Universal Distance-Complete Core Pair-Deletion Family Theorem (`∀ C P F a b K`):**
if `C` is a distance-complete core of `P` containing diameter pair `(a, b)`, and `F` is a
finite family of pairs `(u, v)` in `P \ C` (`u ≠ v`) with `K ≤ (F.image (fun p => pairDelScore P p.1 p.2)).card`,
then there exists a family `G` of `K` pairwise nonsimilar `(P.card - 2)`-point pair-deletions
of `P`, all preserving `distanceSet P` and `distinctDistances P` (and certifying
`HasAtLeastKNonsimilarMinimizers K (P.card - 2)` whenever `distinctDistances P ≤ d(P.card - 2)`). -/
theorem distance_complete_core_pair_deletion_family_of_le_card_image_pairDelScore
    (C P : Finset Plane) (F : Finset (Plane × Plane)) (a b : Plane) (K : ℕ)
    (hC : IsDistanceCompleteCore C P) (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist a b)
    (hF : ∀ p ∈ F, p.1 ∈ P ∧ p.2 ∈ P ∧ p.1 ≠ p.2 ∧ p.1 ∉ C ∧ p.2 ∉ C)
    (hK : K ≤ (F.image (fun p => pairDelScore P p.1 p.2)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = P.card - 2 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
        distinctDistances A = distinctDistances P) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances P ≤ minimalDistinctDistances (P.card - 2) →
      HasAtLeastKNonsimilarMinimizers K (P.card - 2)) := by
  obtain ⟨U0, hU0_sub, hU0_card, hU0_inj⟩ :=
    exists_rep_subset_card_eq_image F (fun p : Plane × Plane => pairDelScore P p.1 p.2)
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq (s := U0) (by omega : K ≤ U0.card)
  have hUF : U ⊆ F := hU_sub.trans hU0_sub
  let g : Plane × Plane → Finset Plane := fun p => (P.erase p.1).erase p.2
  have haP : a ∈ P := hC.1 haC
  have hbP : b ∈ P := hC.1 hbC
  have hns : ∀ p ∈ U, ∀ q ∈ U, p ≠ q → ¬ DilationEquivSimilar (g p) (g q) := by
    intro p hp q hq hpq
    obtain ⟨hp1P, hp2P, hp12, hp1C, hp2C⟩ := hF p (hUF hp)
    obtain ⟨hq1P, hq2P, hq12, hq1C, hq2C⟩ := hF q (hUF hq)
    have hne_score := hU0_inj p (hU_sub hp) q (hU_sub hq) hpq
    exact nonsimilar_pair_erase_of_pairDelScore_ne P a b p.1 p.2 q.1 q.2 hab haP hbP
      hp1P hp2P hp12 hq1P hq2P hq12
      ⟨fun h => hp1C (h ▸ haC), fun h => hp2C (h ▸ haC)⟩
      ⟨fun h => hp1C (h ▸ hbC), fun h => hp2C (h ▸ hbC)⟩
      ⟨fun h => hq1C (h ▸ haC), fun h => hq2C (h ▸ haC)⟩
      ⟨fun h => hq1C (h ▸ hbC), fun h => hq2C (h ▸ hbC)⟩
      hdiam hne_score
  have hg_inj : Set.InjOn g (U : Set (Plane × Plane)) := by
    intro p hp q hq heq
    by_contra hpq
    apply hns p hp q hq hpq
    rw [heq]
    exact similar_refl (g q)
  have hG_card : (U.image g).card = K := by
    rw [Finset.card_image_of_injOn hg_inj, hU_card]
  have hG_props : ∀ A ∈ U.image g, A.card = P.card - 2 ∧
      Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances A = distinctDistances P := by
    intro A hA
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hp1P, hp2P, hp12, hp1C, hp2C⟩ := hF p (hUF hp)
    obtain ⟨hDS, hdist⟩ := distanceSet_pair_erase_eq_of_isDistanceCompleteCore C P p.1 p.2 hC hp1C hp2C
    have hp2_er : p.2 ∈ P.erase p.1 := Finset.mem_erase.mpr ⟨hp12.symm, hp2P⟩
    have hcard : (g p).card = P.card - 2 := by
      change ((P.erase p.1).erase p.2).card = P.card - 2
      rw [Finset.card_erase_of_mem hp2_er, Finset.card_erase_of_mem hp1P]
      omega
    exact ⟨hcard, hDS, hdist⟩
  have hG_ns : ∀ A ∈ U.image g, ∀ B ∈ U.image g, A ≠ B → ¬ DilationEquivSimilar A B := by
    intro A hA B hB hAB
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact hns p hp q hq (fun h => hAB (congrArg g h))
  refine ⟨⟨U.image g, hG_card, hG_props, hG_ns⟩, ?_⟩
  intro hmin
  refine ⟨U.image g, hG_card, ?_, hG_ns⟩
  intro A hA
  obtain ⟨hcard, _, hdist⟩ := hG_props A hA
  have hlo := minimal_le A (P.card - 2) hcard
  exact ⟨hcard, by omega⟩

end Erdos91.PairDeletionInvariantsAndMultiplicity


/-! ## Suite 3: Universal Equilateral Triangular Lattice Patches `T_L = hexSet L 0 (L - 1)` and Upper-Left Half-Triangle Distance-Complete Cores (`∀ L ≥ 1`) -/

namespace Erdos91.EquilateralTriangularPatchCoreAndPairDeletions
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
  Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions

/-- Coordinate set `triPatchCoords L = hexCoords L 0 (L - 1)` of the equilateral triangular
lattice patch `T_L` of side length `L - 1` (`|T_L| = L(L+1)/2`). -/
def triPatchCoords (L : ℕ) : Finset (ℕ × ℕ) :=
  hexCoords L 0 (L - 1)

/-- Planar point set `triPatchSet L = hexSet L 0 (L - 1)` of the equilateral triangular
lattice patch `T_L`. -/
noncomputable def triPatchSet (L : ℕ) : Finset Plane :=
  hexSet L 0 (L - 1)

/-- Upper-left half-triangle coordinate core `triPatchCoreCoords L = insert (0, 0) (triUtp (L - 1))`
(`{(x, y) ∈ T_L : x ≤ y}`). -/
def triPatchCoreCoords (L : ℕ) : Finset (ℕ × ℕ) :=
  insert (0, 0) (triUtp (L - 1))

/-- Upper-left half-triangle planar core `triPatchCore L = (triPatchCoreCoords L).image triPoint`. -/
noncomputable def triPatchCore (L : ℕ) : Finset Plane :=
  (triPatchCoreCoords L).image triPoint

/-- Exact membership characterization of `triPatchCoords L` for `L ≥ 1`:
`p ∈ triPatchCoords L ↔ p.1 + p.2 ≤ L - 1`. -/
theorem mem_triPatchCoords_iff (L : ℕ) (hL : 1 ≤ L) (p : ℕ × ℕ) :
    p ∈ triPatchCoords L ↔ p.1 + p.2 ≤ L - 1 := by
  unfold triPatchCoords
  rw [mem_hexCoords_iff]
  omega

/-- For `L ≥ 1`, `triPatchCoreCoords L ⊆ triPatchCoords L`. -/
theorem triPatchCoreCoords_subset_triPatchCoords (L : ℕ) (hL : 1 ≤ L) :
    triPatchCoreCoords L ⊆ triPatchCoords L := by
  intro u hu
  unfold triPatchCoreCoords at hu
  obtain ⟨_, hsum⟩ := mem_insert_zero_triUtp_bounds (L - 1) hu
  exact (mem_triPatchCoords_iff L hL u).mpr hsum

/-- Canonical offset from `(0, 0)` to any `u` with `u.1 ≤ u.2` is `u` itself. -/
theorem triOffset_zero_eq {u : ℕ × ℕ} (hu : u.1 ≤ u.2) :
    triOffset (0, 0) u = u := by
  rcases u with ⟨x, y⟩
  dsimp at hu
  unfold triOffset
  dsimp
  have hdx : Nat.dist 0 x = x := by unfold Nat.dist; omega
  have hdy : Nat.dist 0 y = y := by unfold Nat.dist; omega
  rw [hdx, hdy]
  split_ifs <;> rfl

/-- Euclidean distance from `triPoint (0, 0)` to `triPoint u` (`u.1 ≤ u.2`) equals `triNorm u`. -/
theorem dist_triPoint_zero_eq {u : ℕ × ℕ} (hu : u.1 ≤ u.2) :
    dist (triPoint (0, 0)) (triPoint u) = triNorm u := by
  rw [dist_triPoint_eq (0, 0) u, triOffset_zero_eq hu]

/-- **Universal Equilateral Triangular Patch Distance-Complete Core Theorem (`∀ L ≥ 1`):**
for every `L ≥ 1`, both `triPatchCore L` and `triPatchSet L` have exact distance set
`(triUtp (L - 1)).image triNorm` and distinct-distance count
`((triUtp (L - 1)).image triNormSq).card`, so the upper-left half-triangle `triPatchCore L`
is a universal distance-complete core of `triPatchSet L` (`IsDistanceCompleteCore (triPatchCore L) (triPatchSet L)`). -/
theorem distanceSet_triPatchCore_eq_and_isDistanceCompleteCore (L : ℕ) (hL : 1 ≤ L) :
    Erdos91.DistanceErasure.distanceSet (triPatchCore L) = (triUtp (L - 1)).image triNorm ∧
      Erdos91.DistanceErasure.distanceSet (triPatchSet L) = (triUtp (L - 1)).image triNorm ∧
      distinctDistances (triPatchSet L) = ((triUtp (L - 1)).image triNormSq).card ∧
      IsDistanceCompleteCore (triPatchCore L) (triPatchSet L) := by
  have hsub_core_set : triPatchCore L ⊆ triPatchSet L := by
    unfold triPatchCore triPatchSet hexSet
    exact Finset.image_subset_image (triPatchCoreCoords_subset_triPatchCoords L hL)
  have hsub_upper : Erdos91.DistanceErasure.distanceSet (triPatchSet L) ⊆
      (triUtp (L - 1)).image triNorm :=
    distanceSet_hexSet_subset L 0 (L - 1) (by omega)
  have hsub_lower : (triUtp (L - 1)).image triNorm ⊆
      Erdos91.DistanceErasure.distanceSet (triPatchCore L) := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hne0, hle, _⟩ := (mem_triUtp_iff (L - 1) u).mp hu
    have hp : triPoint (0, 0) ∈ triPatchCore L :=
      Finset.mem_image_of_mem triPoint (Finset.mem_insert_self (0, 0) (triUtp (L - 1)))
    have hq : triPoint u ∈ triPatchCore L :=
      Finset.mem_image_of_mem triPoint (Finset.mem_insert_of_mem hu)
    have hpq : triPoint (0, 0) ≠ triPoint u := fun h => hne0 (triPoint_injective h).symm
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint (0, 0), hp, triPoint u, hq, hpq, dist_triPoint_zero_eq hle⟩
  have hDS_core : Erdos91.DistanceErasure.distanceSet (triPatchCore L) =
      (triUtp (L - 1)).image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core_set).trans hsub_upper) hsub_lower
  have hDS_set : Erdos91.DistanceErasure.distanceSet (triPatchSet L) =
      (triUtp (L - 1)).image triNorm :=
    Finset.Subset.antisymm hsub_upper (hsub_lower.trans (distanceSet_mono hsub_core_set))
  have hdist : distinctDistances (triPatchSet L) = ((triUtp (L - 1)).image triNormSq).card := by
    change (Erdos91.DistanceErasure.distanceSet (triPatchSet L)).card = _
    rw [hDS_set, card_image_triNorm_eq_card_image_triNormSq]
  exact ⟨hDS_core, hDS_set, hdist, ⟨hsub_core_set, hDS_core.trans hDS_set.symm⟩⟩

/-- **Universal Lower-Right Sub-Triangle Deletability (`∀ L ≥ 1, ∀ p`):**
every lattice point `p = (x, y)` in the strict lower-right sub-triangle (`y < x` and
`x + y ≤ L - 1`) belongs to `triPatchSet L` and lies outside `triPatchCore L`. -/
theorem lowerRight_mem_sdiff_triPatchCore (L : ℕ) (hL : 1 ≤ L) {p : ℕ × ℕ}
    (hlt : p.2 < p.1) (hsum : p.1 + p.2 ≤ L - 1) :
    triPoint p ∈ triPatchSet L ∧ triPoint p ∉ triPatchCore L := by
  refine ⟨Finset.mem_image_of_mem triPoint ((mem_triPatchCoords_iff L hL p).mpr hsum), ?_⟩
  intro hmem
  unfold triPatchCore at hmem
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
  have hup : u = p := triPoint_injective heq
  subst hup
  obtain ⟨hle, _⟩ := mem_insert_zero_triUtp_bounds (L - 1) hu
  omega

/-- **Universal `k`-Deletion Distance-Set Invariance on `triPatchSet L` (`∀ L ≥ 1, ∀ D`):**
deleting any subset `D` disjoint from `triPatchCore L` (in particular any subset of
the lower-right sub-triangle `{y < x}`) from `triPatchSet L` preserves both the
distance set `(triUtp (L - 1)).image triNorm` and distinct-distance count of `triPatchSet L`. -/
theorem triPatchSet_sdiff_distanceSet_eq (L : ℕ) (hL : 1 ≤ L) (D : Finset Plane)
    (hDC : Disjoint D (triPatchCore L)) :
    Erdos91.DistanceErasure.distanceSet (triPatchSet L \ D) = (triUtp (L - 1)).image triNorm ∧
      distinctDistances (triPatchSet L \ D) = ((triUtp (L - 1)).image triNormSq).card := by
  obtain ⟨_, hDS_set, hdist, hCore⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore L hL
  obtain ⟨hDS, hdd⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore
    (triPatchCore L) (triPatchSet L) D hCore hDC
  exact ⟨hDS.trans hDS_set, hdd.trans hdist⟩

/-- **Universal Pair-Deletion Distance-Set Invariance on `triPatchSet L` (`∀ L ≥ 1, ∀ p q`):**
for every `L ≥ 1` and any two lower-right vertices `p, q` with `p.2 < p.1` and `q.2 < q.1`,
deleting `triPoint p` and `triPoint q` from `triPatchSet L` preserves the exact distance set
`(triUtp (L - 1)).image triNorm` and distinct-distance count of `triPatchSet L`. -/
theorem triPatchSet_pair_erase_distanceSet_eq (L : ℕ) (hL : 1 ≤ L) {p q : ℕ × ℕ}
    (hp : p.2 < p.1) (hq : q.2 < q.1) :
    Erdos91.DistanceErasure.distanceSet (((triPatchSet L).erase (triPoint p)).erase (triPoint q)) =
        (triUtp (L - 1)).image triNorm ∧
      distinctDistances (((triPatchSet L).erase (triPoint p)).erase (triPoint q)) =
        distinctDistances (triPatchSet L) := by
  obtain ⟨_, hDS_set, _, hCore⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore L hL
  have hp_not : triPoint p ∉ triPatchCore L := by
    intro hmem
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
    have hup := triPoint_injective heq
    subst hup
    obtain ⟨hle, _⟩ := mem_insert_zero_triUtp_bounds (L - 1) hu
    omega
  have hq_not : triPoint q ∉ triPatchCore L := by
    intro hmem
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
    have huq := triPoint_injective heq
    subst huq
    obtain ⟨hle, _⟩ := mem_insert_zero_triUtp_bounds (L - 1) hu
    omega
  obtain ⟨hDS, hdd⟩ := distanceSet_pair_erase_eq_of_isDistanceCompleteCore
    (triPatchCore L) (triPatchSet L) (triPoint p) (triPoint q) hCore hp_not hq_not
  exact ⟨hDS.trans hDS_set, hdd⟩

end Erdos91.EquilateralTriangularPatchCoreAndPairDeletions


/-! ## Suite 4: Universal Right-Half Distance-Complete Core on Regular Hexagonal Patches `H_R = hexSet (2R+1) R (2R)` (`∀ R : ℕ`) -/

namespace Erdos91.HexagonalPatchRightCoreAndPairDeletions
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
  Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions

/-- Right-half coordinate core `hexRightCoreCoords R` of `hexCoords (2R+1) R (2R)`,
containing the left diameter endpoint `(0, R)`, base anchor `(R, 0)`, and all offset
anchors `(R + u.1, u.2)` for `u ∈ triUtp (2 * R)` (which includes the right diameter
endpoint `(2 * R, R)` when `R ≥ 1`). -/
def hexRightCoreCoords (R : ℕ) : Finset (ℕ × ℕ) :=
  insert (0, R) (insert (R, 0) ((triUtp (2 * R)).image (fun u => (R + u.1, u.2))))

/-- Right-half planar core `hexRightCore R = (hexRightCoreCoords R).image triPoint` of
the regular hexagonal lattice patch `hexSet (2 * R + 1) R (2 * R)`. -/
noncomputable def hexRightCore (R : ℕ) : Finset Plane :=
  (hexRightCoreCoords R).image triPoint

/-- For every `R : ℕ`, `hexRightCoreCoords R ⊆ hexCoords (2 * R + 1) R (2 * R)`. -/
theorem hexRightCoreCoords_subset_hexCoords (R : ℕ) :
    hexRightCoreCoords R ⊆ hexCoords (2 * R + 1) R (2 * R) := by
  intro p hp
  unfold hexRightCoreCoords at hp
  simp only [Finset.mem_insert, Finset.mem_image] at hp
  rcases hp with rfl | rfl | ⟨u, hu, rfl⟩
  · exact mem_hexCoords_diam_left R
  · exact mem_hexCoords_base_anchor R
  · exact mem_hexCoords_offset_of_mem_triUtp R hu

/-- **Universal Hexagonal Right-Half Distance-Complete Core Theorem (`∀ R : ℕ`):**
for every `R : ℕ`, `hexRightCore R` is a distance-complete core of
`hexSet (2 * R + 1) R (2 * R)` with exact distance set `(triUtp (2 * R)).image triNorm`. -/
theorem hexRightCore_isDistanceCompleteCore (R : ℕ) :
    IsDistanceCompleteCore (hexRightCore R) (hexSet (2 * R + 1) R (2 * R)) ∧
      Erdos91.DistanceErasure.distanceSet (hexRightCore R) = (triUtp (2 * R)).image triNorm := by
  have hsub_core : hexRightCore R ⊆ hexSet (2 * R + 1) R (2 * R) :=
    Finset.image_subset_image (hexRightCoreCoords_subset_hexCoords R)
  have hDS_hex := distanceSet_hexSet_regular_eq R
  have hsub_ds : Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R)) ⊆
      Erdos91.DistanceErasure.distanceSet (hexRightCore R) := by
    rw [hDS_hex]
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hne0, hle, _⟩ := (mem_triUtp_iff (2 * R) u).mp hu
    have hp_coord : (R, 0) ∈ hexRightCoreCoords R := by
      unfold hexRightCoreCoords; simp
    have hq_coord : (R + u.1, u.2) ∈ hexRightCoreCoords R := by
      unfold hexRightCoreCoords
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hu))
    have hp : triPoint (R, 0) ∈ hexRightCore R := Finset.mem_image_of_mem triPoint hp_coord
    have hq : triPoint (R + u.1, u.2) ∈ hexRightCore R := Finset.mem_image_of_mem triPoint hq_coord
    have hpq : triPoint (R, 0) ≠ triPoint (R + u.1, u.2) := by
      intro heq
      have hinj := triPoint_injective heq
      simp only [Prod.mk.injEq] at hinj
      exact hne0 (Prod.ext (by omega) (by omega))
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint (R, 0), hp, triPoint (R + u.1, u.2), hq, hpq, dist_triPoint_base_anchor_eq R hle⟩
  have hCore : IsDistanceCompleteCore (hexRightCore R) (hexSet (2 * R + 1) R (2 * R)) :=
    (isDistanceCompleteCore_iff_subset _ _).mpr ⟨hsub_core, hsub_ds⟩
  exact ⟨hCore, hCore.2.trans hDS_hex⟩

/-- Every left-half point `p = (x, y)` with `x < R` and `p ≠ (0, R)` lies outside `hexRightCore R`. -/
theorem leftHalf_notMem_hexRightCore (R : ℕ) {p : ℕ × ℕ}
    (hx : p.1 < R) (hne : p ≠ (0, R)) :
    triPoint p ∉ hexRightCore R := by
  intro hmem
  unfold hexRightCore at hmem
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hmem
  have hqp : q = p := triPoint_injective heq
  subst hqp
  unfold hexRightCoreCoords at hq
  simp only [Finset.mem_insert, Finset.mem_image] at hq
  rcases hq with h0R | hR0 | ⟨u, _, hu_eq⟩
  · exact hne h0R
  · rw [hR0] at hx; dsimp at hx; omega
  · rw [← hu_eq] at hx; dsimp at hx; omega

/-- **Universal Left-Half Pair-Deletion Distance-Set Invariance on `hexSet (2R+1) R (2R)` (`∀ R p q`):**
for every `R : ℕ` and any two left-half coordinates `p, q` with `p.1 < R`, `p ≠ (0, R)`,
`q.1 < R`, `q ≠ (0, R)`, deleting `triPoint p` and `triPoint q` from
`hexSet (2 * R + 1) R (2 * R)` preserves the exact distance set `(triUtp (2 * R)).image triNorm`
and distinct-distance count `((triUtp (2 * R)).image triNormSq).card`. -/
theorem hexSet_pair_erase_leftHalf_distanceSet_eq (R : ℕ) {p q : ℕ × ℕ}
    (hxp : p.1 < R) (hnep : p ≠ (0, R)) (hxq : q.1 < R) (hneq : q ≠ (0, R)) :
    Erdos91.DistanceErasure.distanceSet
        (((hexSet (2 * R + 1) R (2 * R)).erase (triPoint p)).erase (triPoint q)) =
      (triUtp (2 * R)).image triNorm ∧
    distinctDistances (((hexSet (2 * R + 1) R (2 * R)).erase (triPoint p)).erase (triPoint q)) =
      ((triUtp (2 * R)).image triNormSq).card := by
  obtain ⟨hCore, _⟩ := hexRightCore_isDistanceCompleteCore R
  obtain ⟨hDS, hdd⟩ := distanceSet_pair_erase_eq_of_isDistanceCompleteCore
    (hexRightCore R) (hexSet (2 * R + 1) R (2 * R)) (triPoint p) (triPoint q)
    hCore (leftHalf_notMem_hexRightCore R hxp hnep) (leftHalf_notMem_hexRightCore R hxq hneq)
  exact ⟨hDS.trans (distanceSet_hexSet_regular_eq R),
    hdd.trans (distinctDistances_hexSet_regular_eq R)⟩

end Erdos91.HexagonalPatchRightCoreAndPairDeletions


/-! ## Suite 5: Universal Integer-Lattice `hexCoordPairDelScore` Bridge and Certified `n = 10, 11, 13, 17, 19` Pair-Deletion Families (`∀ k c m K`) -/

namespace Erdos91.TruncatedTriangleAndEquilateralPatchFamilies
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.PairDeletionInvariantsAndMultiplicity
  Erdos91.EquilateralTriangularPatchCoreAndPairDeletions
  Erdos91.HexagonalPatchRightCoreAndPairDeletions
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
  Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions
  Erdos91.UnconditionalNaturalDensityOne
  Erdos91.ExactGridEnergyAndDeletionFamilies
  Erdos91.ThreeUniqueMinimizer
  Erdos91.TwoDistanceCapAndSixNonunique
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Exact integer lattice row energy `∑ q ∈ hexCoords k c m, triNormSq (triOffset p q)`. -/
def hexCoordEnergy (k c m : ℕ) (p : ℕ × ℕ) : ℕ :=
  (hexCoords k c m).sum (fun q => triNormSq (triOffset p q))

/-- Exact integer lattice pair-deletion score `hexCoordEnergy k c m p + hexCoordEnergy k c m q - triNormSq (triOffset p q)`. -/
def hexCoordPairDelScore (k c m : ℕ) (p q : ℕ × ℕ) : ℕ :=
  hexCoordEnergy k c m p + hexCoordEnergy k c m q - triNormSq (triOffset p q)

/-- 4-point coordinate core `truncTriCore4Coords = {(0, 1), (0, 2), (1, 3), (3, 1)}` of `hexCoords 4 1 3`. -/
def truncTriCore4Coords : Finset (ℕ × ℕ) :=
  {(0, 1), (0, 2), (1, 3), (3, 1)}

/-- Ordered off-diagonal pairs in the 8-point complement `hexCoords 4 1 3 \ truncTriCore4Coords`. -/
def truncTriCompPairs : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (hexCoords 4 1 3 \ truncTriCore4Coords).offDiag

/-- Ordered off-diagonal pairs in the 6-point lower-right complement `triPatchCoords 5 \ triPatchCoreCoords 5`. -/
def triPatch5CompPairs : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (triPatchCoords 5 \ triPatchCoreCoords 5).offDiag

/-- Ordered off-diagonal pairs in the 9-point left-half complement `hexCoords 5 2 4 \ hexRightCoreCoords 2`. -/
def hex2LeftCompPairs : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (hexCoords 5 2 4 \ hexRightCoreCoords 2).offDiag

/-- Ordered off-diagonal pairs in the 9-point lower-right complement `triPatchCoords 6 \ triPatchCoreCoords 6`. -/
def triPatch6CompPairs : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (triPatchCoords 6 \ triPatchCoreCoords 6).offDiag

private theorem card_image_truncTriCompPairs :
    (truncTriCompPairs.image (fun pq => hexCoordPairDelScore 4 1 3 pq.1 pq.2)).card = 12 := rfl

private theorem card_image_triPatch5CompPairs :
    (triPatch5CompPairs.image (fun pq => hexCoordPairDelScore 5 0 4 pq.1 pq.2)).card = 12 := rfl

private theorem card_image_hex2LeftCompPairs :
    (hex2LeftCompPairs.image (fun pq => hexCoordPairDelScore 5 2 4 pq.1 pq.2)).card = 15 := rfl

private theorem card_image_triPatch6CompPairs :
    (triPatch6CompPairs.image (fun pq => hexCoordPairDelScore 6 0 5 pq.1 pq.2)).card = 25 := rfl

private theorem card_image_truncTriCompSingle :
    ((hexCoords 4 1 3 \ truncTriCore4Coords).image (hexCoordEnergy 4 1 3)).card = 3 := rfl

private theorem card_image_triPatch5CompSingle :
    ((triPatchCoords 5 \ triPatchCoreCoords 5).image (hexCoordEnergy 5 0 4)).card = 4 := rfl

private theorem card_image_triPatch6CompSingle :
    ((triPatchCoords 6 \ triPatchCoreCoords 6).image (hexCoordEnergy 6 0 5)).card = 5 := rfl

open scoped Classical

/-- Universal membership lemma for off-diagonal pairs of `P_coords \ C_coords`. -/
theorem mem_sdiff_offDiag_props {P_coords C_coords : Finset (ℕ × ℕ)}
    {pq : (ℕ × ℕ) × (ℕ × ℕ)} (hpq : pq ∈ (P_coords \ C_coords).offDiag) :
    pq.1 ∈ P_coords ∧ pq.2 ∈ P_coords ∧ pq.1 ≠ pq.2 ∧ pq.1 ∉ C_coords ∧ pq.2 ∉ C_coords := by
  obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.mp hpq
  obtain ⟨hp1, hn1⟩ := Finset.mem_sdiff.mp h1
  obtain ⟨hp2, hn2⟩ := Finset.mem_sdiff.mp h2
  exact ⟨hp1, hp2, hne, hn1, hn2⟩

/-- **Universal Integer-Lattice Row-Energy Identity (`∀ k c m p`):**
the Euclidean vertex energy `energy (hexSet k c m) (triPoint p)` equals `(hexCoordEnergy k c m p : ℝ)`. -/
theorem energy_hexSet_eq_hexCoordEnergy (k c m : ℕ) (p : ℕ × ℕ) :
    energy (hexSet k c m) (triPoint p) = ((hexCoordEnergy k c m p : ℕ) : ℝ) := by
  unfold energy hexSet hexCoordEnergy
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h)]
  push_cast
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact dist_triPoint_sq_eq_triNormSq p q

/-- **Universal Integer-Lattice Pair-Deletion Score Identity (`∀ k c m p q`):**
for any `p : ℕ × ℕ` and `q ∈ hexCoords k c m`,
`pairDelScore (hexSet k c m) (triPoint p) (triPoint q) = (hexCoordPairDelScore k c m p q : ℝ)`. -/
theorem pairDelScore_hexSet_eq_hexCoordPairDelScore (k c m : ℕ) (p q : ℕ × ℕ)
    (hq : q ∈ hexCoords k c m) :
    pairDelScore (hexSet k c m) (triPoint p) (triPoint q) =
      ((hexCoordPairDelScore k c m p q : ℕ) : ℝ) := by
  unfold pairDelScore hexCoordPairDelScore
  rw [energy_hexSet_eq_hexCoordEnergy, energy_hexSet_eq_hexCoordEnergy,
    dist_triPoint_sq_eq_triNormSq]
  have hle : triNormSq (triOffset p q) ≤ hexCoordEnergy k c m p := by
    unfold hexCoordEnergy
    exact Finset.single_le_sum (f := fun x => triNormSq (triOffset p x))
      (fun _ _ => Nat.zero_le _) hq
  have hle2 : triNormSq (triOffset p q) ≤ hexCoordEnergy k c m p + hexCoordEnergy k c m q :=
    hle.trans (Nat.le_add_right _ _)
  push_cast [hle2]
  rfl

/-- **Universal Diameter Bound on `hexSet k c m` (`∀ k c m a b x y`):**
if `k ≤ m + 1` and `dist a b ^ 2 = 4 * m^2`, then every `x, y ∈ hexSet k c m`
satisfies `dist x y ≤ dist a b`. -/
theorem dist_le_of_mem_hexSet_of_dist_sq_eq (k c m : ℕ) (hkm : k ≤ m + 1)
    (a b : Plane) (hdiam_sq : dist a b ^ 2 = ((4 * m * m : ℕ) : ℝ))
    {x y : Plane} (hx : x ∈ hexSet k c m) (hy : y ∈ hexSet k c m) :
    dist x y ≤ dist a b := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  by_cases hpq : p = q
  · subst hpq; rw [dist_self]; exact dist_nonneg
  · have hutp := triOffset_mem_triUtp k c m hkm p q hpq hp hq
    obtain ⟨_, _, hsum⟩ := (mem_triUtp_iff m (triOffset p q)).mp hutp
    have h1 := triNormSq_le_four_mul_add_sq (triOffset p q)
    have h3 : ((triOffset p q).1 + (triOffset p q).2) * ((triOffset p q).1 + (triOffset p q).2) ≤
        m * m := Nat.mul_le_mul hsum hsum
    have h4 : 4 * (m * m) = 4 * m * m := by ring
    have hnorm : triNormSq (triOffset p q) ≤ 4 * m * m := by omega
    have hsq_le : dist (triPoint p) (triPoint q) ^ 2 ≤ dist a b ^ 2 := by
      rw [dist_triPoint_sq_eq_triNormSq, hdiam_sq]
      exact_mod_cast hnorm
    rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_sq (dist_nonneg (x := a))]
    exact Real.sqrt_le_sqrt hsq_le

/-- **Universal Coordinate-Level Pair-Deletion Family Theorem on `hexSet k c m` (`∀ k c m K`):**
for any `k ≤ m + 1`, any distance-complete core `C_coords ⊆ hexCoords k c m`, any diameter
pair `a_c, b_c ∈ C_coords` with `triNormSq (triOffset a_c b_c) = 4 * m * m` (`m ≥ 1`), and any
finite set `F_coords` of pairs `(p, q)` in `hexCoords k c m \ C_coords` (`p ≠ q`) with
`K ≤ (F_coords.image (fun pq => hexCoordPairDelScore k c m pq.1 pq.2)).card`, there exist
`K` pairwise nonsimilar `((hexSet k c m).card - 2)`-point pair-deletions of `hexSet k c m`
with identical distance set `distanceSet (hexSet k c m)` and distinct-distance count
`distinctDistances (hexSet k c m)`. -/
theorem hexSet_pair_deletion_family_of_coord_core
    (k c m K : ℕ) (hkm : k ≤ m + 1) (hm : 1 ≤ m)
    (C_coords : Finset (ℕ × ℕ)) (F_coords : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (a_c b_c : ℕ × ℕ)
    (hCore : IsDistanceCompleteCore (C_coords.image triPoint) (hexSet k c m))
    (ha_c : a_c ∈ C_coords) (hb_c : b_c ∈ C_coords)
    (hdiam_norm : triNormSq (triOffset a_c b_c) = 4 * m * m)
    (hF : ∀ pq ∈ F_coords, pq.1 ∈ hexCoords k c m ∧ pq.2 ∈ hexCoords k c m ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∉ C_coords ∧ pq.2 ∉ C_coords)
    (hK : K ≤ (F_coords.image (fun pq => hexCoordPairDelScore k c m pq.1 pq.2)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (hexSet k c m).card - 2 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet k c m) ∧
        distinctDistances A = distinctDistances (hexSet k c m)) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances (hexSet k c m) ≤ minimalDistinctDistances ((hexSet k c m).card - 2) →
      HasAtLeastKNonsimilarMinimizers K ((hexSet k c m).card - 2)) := by
  let C := C_coords.image triPoint
  let P := hexSet k c m
  let mapProd : (ℕ × ℕ) × (ℕ × ℕ) → Plane × Plane := fun pq => (triPoint pq.1, triPoint pq.2)
  have hmap_inj : Function.Injective mapProd := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ h
    simp only [mapProd, Prod.mk.injEq] at h
    exact Prod.ext (triPoint_injective h.1) (triPoint_injective h.2)
  let F := F_coords.image mapProd
  have hab : triPoint a_c ≠ triPoint b_c := by
    intro heq
    have h0 : a_c = b_c := triPoint_injective heq
    subst h0
    have hzero : triNormSq (triOffset a_c a_c) = 0 := by
      unfold triOffset triNormSq
      simp [Nat.dist_self]
    have hpos : 0 < 4 * m * m := by positivity
    omega
  have haC : triPoint a_c ∈ C := Finset.mem_image_of_mem triPoint ha_c
  have hbC : triPoint b_c ∈ C := Finset.mem_image_of_mem triPoint hb_c
  have hdiam_sq : dist (triPoint a_c) (triPoint b_c) ^ 2 = ((4 * m * m : ℕ) : ℝ) := by
    rw [dist_triPoint_sq_eq_triNormSq, hdiam_norm]
  have hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist (triPoint a_c) (triPoint b_c) :=
    fun x hx y hy => dist_le_of_mem_hexSet_of_dist_sq_eq k c m hkm _ _ hdiam_sq hx hy
  have hF_plane : ∀ p ∈ F, p.1 ∈ P ∧ p.2 ∈ P ∧ p.1 ≠ p.2 ∧ p.1 ∉ C ∧ p.2 ∉ C := by
    intro p hp
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hp1, hp2, hne, hn1, hn2⟩ := hF pq hpq
    refine ⟨Finset.mem_image_of_mem triPoint hp1, Finset.mem_image_of_mem triPoint hp2,
      fun h => hne (triPoint_injective h), ?_, ?_⟩
    · intro hmem
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
      exact hn1 (triPoint_injective heq ▸ hu)
    · intro hmem
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hmem
      exact hn2 (triPoint_injective heq ▸ hu)
  have himg_eq : F.image (fun p => pairDelScore P p.1 p.2) =
      (F_coords.image (fun pq => hexCoordPairDelScore k c m pq.1 pq.2)).image (fun s : ℕ => (s : ℝ)) := by
    ext y
    simp only [F, mapProd, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨pq, hpq, rfl⟩, rfl⟩
      have hq_mem := (hF pq hpq).2.1
      exact ⟨hexCoordPairDelScore k c m pq.1 pq.2, ⟨pq, hpq, rfl⟩,
        (pairDelScore_hexSet_eq_hexCoordPairDelScore k c m pq.1 pq.2 hq_mem).symm⟩
    · rintro ⟨s, ⟨pq, hpq, rfl⟩, rfl⟩
      have hq_mem := (hF pq hpq).2.1
      exact ⟨(triPoint pq.1, triPoint pq.2), ⟨pq, hpq, rfl⟩,
        pairDelScore_hexSet_eq_hexCoordPairDelScore k c m pq.1 pq.2 hq_mem⟩
  have hK_plane : K ≤ (F.image (fun p => pairDelScore P p.1 p.2)).card := by
    rw [himg_eq, Finset.card_image_of_injective _ Nat.cast_injective]
    exact hK
  exact distance_complete_core_pair_deletion_family_of_le_card_image_pairDelScore
    C P F (triPoint a_c) (triPoint b_c) K hCore hab haC hbC hdiam hF_plane hK_plane

/-- **Universal Coordinate-Level Single-Deletion Family Theorem on `hexSet k c m` (`∀ k c m K`):**
for any `k ≤ m + 1` (`m ≥ 1`), any distance-complete core `C_coords ⊆ hexCoords k c m`,
any diameter pair `a_c, b_c ∈ C_coords` with `triNormSq (triOffset a_c b_c) = 4 * m * m`,
and any subset `B_coords ⊆ hexCoords k c m \ C_coords` with
`K ≤ (B_coords.image (hexCoordEnergy k c m)).card`, there exist `K` pairwise nonsimilar
`((hexSet k c m).card - 1)`-point single-deletions of `hexSet k c m` all having exact
distance set `distanceSet (hexSet k c m)` and distinct-distance count
`distinctDistances (hexSet k c m)` (and certifying `HasAtLeastKNonsimilarMinimizers K ((hexSet k c m).card - 1)`
whenever `distinctDistances (hexSet k c m) ≤ d((hexSet k c m).card - 1)`). -/
theorem hexSet_single_deletion_family_of_coord_core
    (k c m K : ℕ) (hkm : k ≤ m + 1) (hm : 1 ≤ m)
    (C_coords B_coords : Finset (ℕ × ℕ)) (a_c b_c : ℕ × ℕ)
    (hCore : IsDistanceCompleteCore (C_coords.image triPoint) (hexSet k c m))
    (ha_c : a_c ∈ C_coords) (hb_c : b_c ∈ C_coords)
    (hdiam_norm : triNormSq (triOffset a_c b_c) = 4 * m * m)
    (hB : ∀ u ∈ B_coords, u ∈ hexCoords k c m ∧ u ∉ C_coords)
    (hK : K ≤ (B_coords.image (hexCoordEnergy k c m)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (hexSet k c m).card - 1 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet k c m) ∧
        distinctDistances A = distinctDistances (hexSet k c m)) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances (hexSet k c m) ≤ minimalDistinctDistances ((hexSet k c m).card - 1) →
      HasAtLeastKNonsimilarMinimizers K ((hexSet k c m).card - 1)) := by
  let C := C_coords.image triPoint
  let P := hexSet k c m
  obtain ⟨U0, hU0_sub, hU0_card, hU0_inj⟩ :=
    exists_rep_subset_card_eq_image B_coords (hexCoordEnergy k c m)
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq (s := U0) (by omega : K ≤ U0.card)
  have hUB : U ⊆ B_coords := hU_sub.trans hU0_sub
  let g : ℕ × ℕ → Finset Plane := fun u => P.erase (triPoint u)
  have hab : triPoint a_c ≠ triPoint b_c := by
    intro heq
    have h0 : a_c = b_c := triPoint_injective heq
    subst h0
    have hzero : triNormSq (triOffset a_c a_c) = 0 := by
      unfold triOffset triNormSq
      simp [Nat.dist_self]
    have hpos : 0 < 4 * m * m := by positivity
    omega
  have haP : triPoint a_c ∈ P := hCore.1 (Finset.mem_image_of_mem triPoint ha_c)
  have hbP : triPoint b_c ∈ P := hCore.1 (Finset.mem_image_of_mem triPoint hb_c)
  have hdiam_sq : dist (triPoint a_c) (triPoint b_c) ^ 2 = ((4 * m * m : ℕ) : ℝ) := by
    rw [dist_triPoint_sq_eq_triNormSq, hdiam_norm]
  have hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist (triPoint a_c) (triPoint b_c) :=
    fun x hx y hy => dist_le_of_mem_hexSet_of_dist_sq_eq k c m hkm _ _ hdiam_sq hx hy
  have hns : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ¬ DilationEquivSimilar (g u) (g v) := by
    intro u hu v hv huv
    obtain ⟨hu_hex, hu_notC⟩ := hB u (hUB hu)
    obtain ⟨hv_hex, hv_notC⟩ := hB v (hUB hv)
    have huP : triPoint u ∈ P := Finset.mem_image_of_mem triPoint hu_hex
    have hvP : triPoint v ∈ P := Finset.mem_image_of_mem triPoint hv_hex
    have hua : triPoint u ≠ triPoint a_c := fun h => hu_notC (triPoint_injective h ▸ ha_c)
    have hub : triPoint u ≠ triPoint b_c := fun h => hu_notC (triPoint_injective h ▸ hb_c)
    have hva : triPoint v ≠ triPoint a_c := fun h => hv_notC (triPoint_injective h ▸ ha_c)
    have hvb : triPoint v ≠ triPoint b_c := fun h => hv_notC (triPoint_injective h ▸ hb_c)
    have hne_nat := hU0_inj u (hU_sub hu) v (hU_sub hv) huv
    have hne_en : energy P (triPoint u) ≠ energy P (triPoint v) := by
      rw [energy_hexSet_eq_hexCoordEnergy, energy_hexSet_eq_hexCoordEnergy]
      exact_mod_cast hne_nat
    rw [similar_iff_image]
    exact DeletionEnergy91.nonsimilar_deletions P (triPoint a_c) (triPoint b_c)
      (triPoint u) (triPoint v) hab haP hbP huP hvP hua hub hva hvb hdiam hne_en
  have hg_inj : Set.InjOn g (U : Set (ℕ × ℕ)) := by
    intro u hu v hv heq
    by_contra huv
    apply hns u hu v hv huv
    rw [heq]
    exact similar_refl (g v)
  have hG_card : (U.image g).card = K := by
    rw [Finset.card_image_of_injOn hg_inj, hU_card]
  have hG_props : ∀ A ∈ U.image g, A.card = P.card - 1 ∧
      Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances A = distinctDistances P := by
    intro A hA
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hu_hex, hu_notC⟩ := hB u (hUB hu)
    have huP : triPoint u ∈ P := Finset.mem_image_of_mem triPoint hu_hex
    have hu_notC_plane : triPoint u ∉ C := by
      intro hmem
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hmem
      exact hu_notC (triPoint_injective heq ▸ hw)
    obtain ⟨hDS, hdd⟩ := distanceSet_erase_eq_of_isDistanceCompleteCore C P (triPoint u) hCore hu_notC_plane
    exact ⟨Finset.card_erase_of_mem huP, hDS, hdd⟩
  have hG_ns : ∀ A ∈ U.image g, ∀ B ∈ U.image g, A ≠ B → ¬ DilationEquivSimilar A B := by
    intro A hA B hB hAB
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    exact hns u hu v hv (fun h => hAB (congrArg g h))
  refine ⟨⟨U.image g, hG_card, hG_props, hG_ns⟩, ?_⟩
  intro hmin
  refine ⟨U.image g, hG_card, ?_, hG_ns⟩
  intro A hA
  obtain ⟨hcard, _, hdist⟩ := hG_props A hA
  have hlo := minimal_le A (P.card - 1) hcard
  exact ⟨hcard, le_antisymm (hdist.trans_le hmin) hlo⟩

/-- 4-point planar distance-complete core `truncTriCore4` of the 12-point truncated triangle `hexSet 4 1 3`. -/
noncomputable def truncTriCore4 : Finset Plane :=
  truncTriCore4Coords.image triPoint

/-- **Exact 4-Point Distance-Complete Core Theorem on the 12-Point Patch `hexSet 4 1 3` (`∀ p`):**
every `p ∈ truncTriCore4Coords` maps into `hexSet 4 1 3`, `(hexSet 4 1 3).card = 12`,
`truncTriCore4.card = 4`, `IsDistanceCompleteCore truncTriCore4 (hexSet 4 1 3)`,
`distanceSet (hexSet 4 1 3) = (triUtp 3).image triNorm`, and `distinctDistances (hexSet 4 1 3) = 5`. -/
theorem card_and_distanceSet_hexSet_4_1_3_and_truncTriCore4
    (p : ℕ × ℕ) (hp : p ∈ truncTriCore4Coords) :
    triPoint p ∈ hexSet 4 1 3 ∧
      (hexSet 4 1 3).card = 12 ∧
      truncTriCore4.card = 4 ∧
      IsDistanceCompleteCore truncTriCore4 (hexSet 4 1 3) ∧
      Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) = (triUtp 3).image triNorm ∧
      distinctDistances (hexSet 4 1 3) = 5 := by
  have hcard12 : (hexSet 4 1 3).card = 12 := by rw [card_hexSet]; rfl
  have hcard4 : truncTriCore4.card = 4 := by
    unfold truncTriCore4
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hsub_coords : truncTriCore4Coords ⊆ hexCoords 4 1 3 := by decide
  have hsub_core : truncTriCore4 ⊆ hexSet 4 1 3 := Finset.image_subset_image hsub_coords
  have hupper : Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ⊆ (triUtp 3).image triNorm :=
    distanceSet_hexSet_subset 4 1 3 (by omega)
  have h_edge : ∀ p q : ℕ × ℕ, p ∈ truncTriCore4Coords → q ∈ truncTriCore4Coords → p ≠ q →
      triNorm (triOffset p q) ∈ Erdos91.DistanceErasure.distanceSet truncTriCore4 := by
    intro p q hp hq hpq
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint p, Finset.mem_image_of_mem triPoint hp,
       triPoint q, Finset.mem_image_of_mem triPoint hq,
       fun h => hpq (triPoint_injective h), dist_triPoint_eq p q⟩
  have hlower : (triUtp 3).image triNorm ⊆ Erdos91.DistanceErasure.distanceSet truncTriCore4 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ triUtp 3,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (1, 1) ∨ v = (1, 2) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 1) (0, 2) (by decide) (by decide) (by decide)
    · exact h_edge (1, 3) (3, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 1) (3, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 2) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 1) (1, 3) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet truncTriCore4 = (triUtp 3).image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hupper) hlower
  have hDS_hex : Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) = (triUtp 3).image triNorm :=
    Finset.Subset.antisymm hupper (hlower.trans (distanceSet_mono hsub_core))
  have hCore : IsDistanceCompleteCore truncTriCore4 (hexSet 4 1 3) :=
    ⟨hsub_core, hDS_core.trans hDS_hex.symm⟩
  have hdd : distinctDistances (hexSet 4 1 3) = 5 := by
    change (Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3)).card = 5
    rw [hDS_hex, card_image_triNorm_eq_card_image_triNormSq]
    rfl
  exact ⟨hsub_core (Finset.mem_image_of_mem triPoint hp), hcard12, hcard4, hCore, hDS_hex, hdd⟩

/-- **Universal `k`-Deletion Distance-Set Invariance and Conditional Optimality on `hexSet 4 1 3` (`∀ D k`):**
for every subset `D ⊆ hexSet 4 1 3` disjoint from `truncTriCore4` with `D.card = k`,
`hexSet 4 1 3 \ D` has `12 - k` points, exact distance set `distanceSet (hexSet 4 1 3)`,
and `5` distinct distances (`minimalDistinctDistances (12 - k) ≤ 5`), and is globally
optimal whenever `5 ≤ minimalDistinctDistances (12 - k)`. -/
theorem truncTri_sdiff_distanceSet_and_optimal_of_five_le
    (D : Finset Plane) (k : ℕ) (hDP : D ⊆ hexSet 4 1 3)
    (hDC : Disjoint D truncTriCore4) (hDcard : D.card = k) :
    (hexSet 4 1 3 \ D).card = 12 - k ∧
      Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3 \ D) =
        Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ∧
      distinctDistances (hexSet 4 1 3 \ D) = 5 ∧
      minimalDistinctDistances (12 - k) ≤ 5 ∧
      (5 ≤ minimalDistinctDistances (12 - k) → IsOptimal (hexSet 4 1 3 \ D) (12 - k)) := by
  obtain ⟨_, hcard12, _, hCore, _, hdd5⟩ :=
    card_and_distanceSet_hexSet_4_1_3_and_truncTriCore4 (0, 1) (by decide)
  obtain ⟨hDS, hdd⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore
    truncTriCore4 (hexSet 4 1 3) D hCore hDC
  have hcard : (hexSet 4 1 3 \ D).card = 12 - k := by
    rw [Finset.card_sdiff_of_subset hDP, hcard12, hDcard]
  have hdd_eq : distinctDistances (hexSet 4 1 3 \ D) = 5 := hdd.trans hdd5
  have hmin_le : minimalDistinctDistances (12 - k) ≤ 5 :=
    (minimal_le (hexSet 4 1 3 \ D) (12 - k) hcard).trans hdd_eq.le
  refine ⟨hcard, hDS, hdd_eq, hmin_le, ?_⟩
  intro h5
  exact ⟨hcard, by omega⟩

/-- **Certified 12-Configuration Pair-Deletion Family at `n = 10` on `hexSet 4 1 3` (`∀ K ≤ 12`):**
for every `K ≤ 12`, there exists a family `G` of `K` pairwise nonsimilar `10`-point
pair-deletions of `hexSet 4 1 3`, all sharing the exact 5-element distance set
`distanceSet (hexSet 4 1 3)` (`distinctDistances A = 5`), and if `5 ≤ d(10)` then
`HasAtLeastKNonsimilarMinimizers K 10` holds (`¬ UniqueMinimizer 10`). -/
theorem hexSet_4_1_3_ten_point_pair_deletion_family (K : ℕ) (hK : K ≤ 12) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 10 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ∧
        distinctDistances A = 5) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (5 ≤ minimalDistinctDistances 10 → HasAtLeastKNonsimilarMinimizers K 10) := by
  obtain ⟨_, hcard12, _, hCore, _, hdd5⟩ :=
    card_and_distanceSet_hexSet_4_1_3_and_truncTriCore4 (0, 1) (by decide)
  have hF : ∀ pq ∈ truncTriCompPairs, pq.1 ∈ hexCoords 4 1 3 ∧ pq.2 ∈ hexCoords 4 1 3 ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∉ truncTriCore4Coords ∧ pq.2 ∉ truncTriCore4Coords :=
    fun _ hpq => mem_sdiff_offDiag_props hpq
  have himg := card_image_truncTriCompPairs
  have hres := hexSet_pair_deletion_family_of_coord_core
    4 1 3 K (by omega) (by omega) truncTriCore4Coords truncTriCompPairs (0, 1) (3, 1)
    hCore (by decide) (by decide) rfl hF (by omega)
  simpa only [hcard12, hdd5] using hres

/-- **Certified 12-Configuration Pair-Deletion Family at `n = 13` on `T_5 = triPatchSet 5` (`∀ K ≤ 12`):**
for every `K ≤ 12`, there exists a family `G` of `K` pairwise nonsimilar `13`-point
pair-deletions of the 15-point equilateral triangular patch `triPatchSet 5 = hexSet 5 0 4`,
all sharing the exact 8-element distance set `distanceSet (triPatchSet 5) = (triUtp 4).image triNorm`
(`distinctDistances A = 8`), and if `8 ≤ d(13)` then `HasAtLeastKNonsimilarMinimizers K 13`. -/
theorem triPatchSet_5_thirteen_point_pair_deletion_family (K : ℕ) (hK : K ≤ 12) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 13 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (8 ≤ minimalDistinctDistances 13 → HasAtLeastKNonsimilarMinimizers K 13) := by
  obtain ⟨_, hDS5, hdd5, hCore5⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore 5 (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet 5 0 4) = (triUtp 4).image triNorm at hDS5
  have hcard15 : (hexSet 5 0 4).card = 15 := by rw [card_hexSet]; rfl
  have hdd8 : distinctDistances (hexSet 5 0 4) = 8 := by
    change distinctDistances (triPatchSet 5) = 8
    rw [hdd5]; rfl
  have hF : ∀ pq ∈ triPatch5CompPairs, pq.1 ∈ hexCoords 5 0 4 ∧ pq.2 ∈ hexCoords 5 0 4 ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∉ triPatchCoreCoords 5 ∧ pq.2 ∉ triPatchCoreCoords 5 :=
    fun _ hpq => mem_sdiff_offDiag_props hpq
  have himg := card_image_triPatch5CompPairs
  have hres := hexSet_pair_deletion_family_of_coord_core
    5 0 4 K (by omega) (by omega) (triPatchCoreCoords 5) triPatch5CompPairs (0, 0) (0, 4)
    hCore5 (by decide) (by decide) rfl hF (by omega)
  simpa only [hcard15, hDS5, hdd8] using hres

/-- **Certified 15-Configuration Pair-Deletion Family at `n = 17` on `H_2 = hexSet 5 2 4` (`∀ K ≤ 15`):**
for every `K ≤ 15`, there exists a family `G` of `K` pairwise nonsimilar `17`-point
pair-deletions of the 19-point regular hexagon `hexSet 5 2 4`, all sharing the exact
8-element distance set `(triUtp 4).image triNorm` (`distinctDistances A = 8`), and if
`8 ≤ d(17)` then `HasAtLeastKNonsimilarMinimizers K 17`. -/
theorem hexSet_5_2_4_seventeen_point_pair_deletion_family (K : ℕ) (hK : K ≤ 15) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 17 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (8 ≤ minimalDistinctDistances 17 → HasAtLeastKNonsimilarMinimizers K 17) := by
  obtain ⟨hCore2, _⟩ := hexRightCore_isDistanceCompleteCore 2
  have hcard19 : (hexSet 5 2 4).card = 19 := Erdos91.ExactHexagonDistanceCountsR1To18.card_hexSet_regular_2
  have hDS2 : Erdos91.DistanceErasure.distanceSet (hexSet 5 2 4) = (triUtp 4).image triNorm :=
    distanceSet_hexSet_regular_eq 2
  have hdd8 : distinctDistances (hexSet 5 2 4) = 8 :=
    Erdos91.ExactHexagonDistanceCountsR1To18.distinctDistances_hexSet_regular_2
  have hF : ∀ pq ∈ hex2LeftCompPairs, pq.1 ∈ hexCoords 5 2 4 ∧ pq.2 ∈ hexCoords 5 2 4 ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∉ hexRightCoreCoords 2 ∧ pq.2 ∉ hexRightCoreCoords 2 :=
    fun _ hpq => mem_sdiff_offDiag_props hpq
  have himg := card_image_hex2LeftCompPairs
  have hres := hexSet_pair_deletion_family_of_coord_core
    5 2 4 K (by omega) (by omega) (hexRightCoreCoords 2) hex2LeftCompPairs (0, 2) (4, 2)
    hCore2 (by decide) (by decide) rfl hF (by omega)
  simpa only [hcard19, hDS2, hdd8] using hres

/-- **Certified 25-Configuration Pair-Deletion Family at `n = 19` on `T_6 = triPatchSet 6` (`∀ K ≤ 25`):**
for every `K ≤ 25`, there exists a family `G` of `K` pairwise nonsimilar `19`-point
pair-deletions of the 21-point equilateral triangular patch `triPatchSet 6 = hexSet 6 0 5`,
all sharing the exact 11-element distance set `(triUtp 5).image triNorm`
(`distinctDistances A = 11`). -/
theorem triPatchSet_6_nineteen_point_pair_deletion_family (K : ℕ) (hK : K ≤ 25) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 19 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        distinctDistances A = 11) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (11 ≤ minimalDistinctDistances 19 → HasAtLeastKNonsimilarMinimizers K 19) := by
  obtain ⟨_, hDS6, hdd6, hCore6⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore 6 (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet 6 0 5) = (triUtp 5).image triNorm at hDS6
  have hcard21 : (hexSet 6 0 5).card = 21 := by rw [card_hexSet]; rfl
  have hdd11 : distinctDistances (hexSet 6 0 5) = 11 := by
    change distinctDistances (triPatchSet 6) = 11
    rw [hdd6]; rfl
  have hF : ∀ pq ∈ triPatch6CompPairs, pq.1 ∈ hexCoords 6 0 5 ∧ pq.2 ∈ hexCoords 6 0 5 ∧
      pq.1 ≠ pq.2 ∧ pq.1 ∉ triPatchCoreCoords 6 ∧ pq.2 ∉ triPatchCoreCoords 6 :=
    fun _ hpq => mem_sdiff_offDiag_props hpq
  have himg := card_image_triPatch6CompPairs
  have hres := hexSet_pair_deletion_family_of_coord_core
    6 0 5 K (by omega) (by omega) (triPatchCoreCoords 6) triPatch6CompPairs (0, 0) (0, 5)
    hCore6 (by decide) (by decide) rfl hF (by omega)
  simpa only [hcard21, hDS6, hdd11] using hres

/-- **Certified 3-Configuration Single-Deletion Family at `n = 11` on `hexSet 4 1 3` (`∀ K ≤ 3`):**
for every `K ≤ 3`, there exists a family `G` of `K` pairwise nonsimilar `11`-point
single-deletions of `hexSet 4 1 3` with exact 5-element distance set
`distanceSet (hexSet 4 1 3)` (`distinctDistances A = 5`), and if `5 ≤ d(11)` then
`HasAtLeastKNonsimilarMinimizers K 11` holds (`¬ UniqueMinimizer 11`). -/
theorem hexSet_4_1_3_eleven_point_single_deletion_family (K : ℕ) (hK : K ≤ 3) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 11 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ∧
        distinctDistances A = 5) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (5 ≤ minimalDistinctDistances 11 → HasAtLeastKNonsimilarMinimizers K 11) := by
  obtain ⟨_, hcard12, _, hCore, _, hdd5⟩ :=
    card_and_distanceSet_hexSet_4_1_3_and_truncTriCore4 (0, 1) (by decide)
  have hB : ∀ u ∈ hexCoords 4 1 3 \ truncTriCore4Coords,
      u ∈ hexCoords 4 1 3 ∧ u ∉ truncTriCore4Coords := fun _ hu => Finset.mem_sdiff.mp hu
  have himg := card_image_truncTriCompSingle
  have hres := hexSet_single_deletion_family_of_coord_core
    4 1 3 K (by omega) (by omega) truncTriCore4Coords (hexCoords 4 1 3 \ truncTriCore4Coords)
    (0, 1) (3, 1) hCore (by decide) (by decide) rfl hB (by omega)
  simpa only [hcard12, hdd5] using hres

/-- **Certified 4-Configuration Single-Deletion Family at `n = 14` on `T_5 = triPatchSet 5` (`∀ K ≤ 4`):**
for every `K ≤ 4`, there exists a family `G` of `K` pairwise nonsimilar `14`-point
single-deletions of `triPatchSet 5 = hexSet 5 0 4` with exact 8-element distance set
`(triUtp 4).image triNorm` (`distinctDistances A = 8`). -/
theorem triPatchSet_5_fourteen_point_single_deletion_family (K : ℕ) (hK : K ≤ 4) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 14 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (8 ≤ minimalDistinctDistances 14 → HasAtLeastKNonsimilarMinimizers K 14) := by
  obtain ⟨_, hDS5, hdd5, hCore5⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore 5 (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet 5 0 4) = (triUtp 4).image triNorm at hDS5
  have hcard15 : (hexSet 5 0 4).card = 15 := by rw [card_hexSet]; rfl
  have hdd8 : distinctDistances (hexSet 5 0 4) = 8 := by
    change distinctDistances (triPatchSet 5) = 8
    rw [hdd5]; rfl
  have hB : ∀ u ∈ triPatchCoords 5 \ triPatchCoreCoords 5,
      u ∈ hexCoords 5 0 4 ∧ u ∉ triPatchCoreCoords 5 := fun _ hu => Finset.mem_sdiff.mp hu
  have himg := card_image_triPatch5CompSingle
  have hres := hexSet_single_deletion_family_of_coord_core
    5 0 4 K (by omega) (by omega) (triPatchCoreCoords 5) (triPatchCoords 5 \ triPatchCoreCoords 5)
    (0, 0) (0, 4) hCore5 (by decide) (by decide) rfl hB (by omega)
  simpa only [hcard15, hDS5, hdd8] using hres

/-- **Certified 5-Configuration Single-Deletion Family at `n = 20` on `T_6 = triPatchSet 6` (`∀ K ≤ 5`):**
for every `K ≤ 5`, there exists a family `G` of `K` pairwise nonsimilar `20`-point
single-deletions of `triPatchSet 6 = hexSet 6 0 5` with exact 11-element distance set
`(triUtp 5).image triNorm` (`distinctDistances A = 11`). -/
theorem triPatchSet_6_twenty_point_single_deletion_family (K : ℕ) (hK : K ≤ 5) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 20 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 5).image triNorm ∧
        distinctDistances A = 11) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (11 ≤ minimalDistinctDistances 20 → HasAtLeastKNonsimilarMinimizers K 20) := by
  obtain ⟨_, hDS6, hdd6, hCore6⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore 6 (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet 6 0 5) = (triUtp 5).image triNorm at hDS6
  have hcard21 : (hexSet 6 0 5).card = 21 := by rw [card_hexSet]; rfl
  have hdd11 : distinctDistances (hexSet 6 0 5) = 11 := by
    change distinctDistances (triPatchSet 6) = 11
    rw [hdd6]; rfl
  have hB : ∀ u ∈ triPatchCoords 6 \ triPatchCoreCoords 6,
      u ∈ hexCoords 6 0 5 ∧ u ∉ triPatchCoreCoords 6 := fun _ hu => Finset.mem_sdiff.mp hu
  have himg := card_image_triPatch6CompSingle
  have hres := hexSet_single_deletion_family_of_coord_core
    6 0 5 K (by omega) (by omega) (triPatchCoreCoords 6) (triPatchCoords 6 \ triPatchCoreCoords 6)
    (0, 0) (0, 5) hCore6 (by decide) (by decide) rfl hB (by omega)
  simpa only [hcard21, hDS6, hdd11] using hres

/-- **Conditional `n = 10, 11` Nonuniqueness Dichotomy under `4 ≤ d(10)` (`∀ K₁ ≤ 12, ∀ K₂ ≤ 3`):**
if `4 ≤ d(10)` (which in particular holds whenever `4 ≤ d(8)`), then either:
- `d(10) = d(11) = d(12) = 5`, `HasAtLeastKNonsimilarMinimizers K₁ 10`, and `HasAtLeastKNonsimilarMinimizers K₂ 11`,
- or `d(10) = 4 ∧ d(11) = 5` and `HasAtLeastKNonsimilarMinimizers K₂ 11` (`¬ UniqueMinimizer 11`),
- or `d(10) = d(11) = 4` and `¬ UniqueMinimizer 10`.
In all cases, `¬ UniqueMinimizer 10 ∨ ¬ UniqueMinimizer 11` holds! -/
theorem not_uniqueMinimizer_ten_or_eleven_of_four_le_ten
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 12) (hK₂ : K₂ ≤ 3)
    (h4 : 4 ≤ minimalDistinctDistances 10) :
    (HasAtLeastKNonsimilarMinimizers K₁ 10 ∧ HasAtLeastKNonsimilarMinimizers K₂ 11) ∨
      HasAtLeastKNonsimilarMinimizers K₂ 11 ∨
      (minimalDistinctDistances 10 = 4 ∧ minimalDistinctDistances 11 = 4 ∧ ¬ UniqueMinimizer 10) := by
  have hmono10_11 : minimalDistinctDistances 10 ≤ minimalDistinctDistances 11 :=
    MinimumMonotone91.minimum_monotone (by omega : 10 ≤ 11)
  have hmono11_12 : minimalDistinctDistances 11 ≤ minimalDistinctDistances 12 :=
    MinimumMonotone91.minimum_monotone (by omega : 11 ≤ 12)
  have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
  by_cases h5_10 : 5 ≤ minimalDistinctDistances 10
  · left
    exact ⟨(hexSet_4_1_3_ten_point_pair_deletion_family K₁ hK₁).2 h5_10,
      (hexSet_4_1_3_eleven_point_single_deletion_family K₂ hK₂).2 (by omega)⟩
  · by_cases h5_11 : 5 ≤ minimalDistinctDistances 11
    · right; left
      exact (hexSet_4_1_3_eleven_point_single_deletion_family K₂ hK₂).2 h5_11
    · right; right
      have hd10_4 : minimalDistinctDistances 10 = 4 := by omega
      have hd11_4 : minimalDistinctDistances 11 = 4 := by omega
      have hplat : minimalDistinctDistances 10 = minimalDistinctDistances 11 := by omega
      have hlow : 2 * minimalDistinctDistances 10 < 10 - 1 := by omega
      exact ⟨hd10_4, hd11_4,
        Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
          10 (by omega) hplat hlow⟩

/-- **Unconditional `n = 8, 9, 10, 11` Multiplicity & Plateau Dichotomy (`∀ K₁ ≤ 12, ∀ K₂ ≤ 3`):**
with zero unproved hypotheses, at least one of the following holds:
1. `5 ≤ d(10)` and both `HasAtLeastKNonsimilarMinimizers K₁ 10` and `HasAtLeastKNonsimilarMinimizers K₂ 11` hold,
2. `d(11) = 5` and `HasAtLeastKNonsimilarMinimizers K₂ 11` holds,
3. `d(10) = d(11) ≤ 4` and `¬ UniqueMinimizer 10` holds,
4. `d(8) = d(9) = d(10) = 3 ∧ d(11) = 4 ∧ ¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9`. -/
theorem unconditional_ten_eleven_dichotomy
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 12) (hK₂ : K₂ ≤ 3) :
    (HasAtLeastKNonsimilarMinimizers K₁ 10 ∧ HasAtLeastKNonsimilarMinimizers K₂ 11) ∨
      HasAtLeastKNonsimilarMinimizers K₂ 11 ∨
      ¬ UniqueMinimizer 10 ∨
      (minimalDistinctDistances 8 = 3 ∧ minimalDistinctDistances 9 = 3 ∧
        minimalDistinctDistances 10 = 3 ∧ minimalDistinctDistances 11 = 4 ∧
        ¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9) := by
  have hd7 : minimalDistinctDistances 7 = 3 := minimalDistinctDistances_seven
  have hm78 := MinimumMonotone91.minimum_monotone (by omega : 7 ≤ 8)
  have hm89 := MinimumMonotone91.minimum_monotone (by omega : 8 ≤ 9)
  have hm910 := MinimumMonotone91.minimum_monotone (by omega : 9 ≤ 10)
  have hm1011 := MinimumMonotone91.minimum_monotone (by omega : 10 ≤ 11)
  have hm1112 := MinimumMonotone91.minimum_monotone (by omega : 11 ≤ 12)
  have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
  by_cases h4 : 4 ≤ minimalDistinctDistances 10
  · rcases not_uniqueMinimizer_ten_or_eleven_of_four_le_ten K₁ K₂ hK₁ hK₂ h4 with h1 | h2 | ⟨_, _, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
  · have hd10_3 : minimalDistinctDistances 10 = 3 := by omega
    have hd9_3 : minimalDistinctDistances 9 = 3 := by omega
    have hd8_3 : minimalDistinctDistances 8 = 3 := by omega
    by_cases h5_11 : 5 ≤ minimalDistinctDistances 11
    · exact Or.inr (Or.inl ((hexSet_4_1_3_eleven_point_single_deletion_family K₂ hK₂).2 h5_11))
    · by_cases h4_11 : minimalDistinctDistances 11 = 4
      · right; right; right
        have hplat89 : minimalDistinctDistances 8 = minimalDistinctDistances (8 + 1) :=
          hd8_3.trans hd9_3.symm
        have hplat910 : minimalDistinctDistances 9 = minimalDistinctDistances (9 + 1) :=
          hd9_3.trans hd10_3.symm
        have hnu8 : ¬ UniqueMinimizer 8 :=
          Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
            8 (by omega) hplat89 (by omega)
        have hnu9 : ¬ UniqueMinimizer 9 :=
          Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
            9 (by omega) hplat910 (by omega)
        exact ⟨hd8_3, hd9_3, hd10_3, h4_11, hnu8, hnu9⟩
      · right; right; left
        have hd11_3 : minimalDistinctDistances 11 = 3 := by omega
        have hplat1011 : minimalDistinctDistances 10 = minimalDistinctDistances (10 + 1) :=
          hd10_3.trans hd11_3.symm
        exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
          10 (by omega) hplat1011 (by omega)

end Erdos91.TruncatedTriangleAndEquilateralPatchFamilies


/-! ## Multi-deletion score invariants and rounded hexagon families -/

/-!
# Universal `k`-Deletion Score Invariants, 3-Distance Level & Diameter-Fiber Bounds, and Rounded/Half-Corner Hexagonal Patch Multiplicity for `n = 8..18` (Erdős Problem #91)
-/

namespace Erdos91.ThreeDistanceLevelAndDiameterFiberBounds
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91 Erdos91.EnergyLevelInvariance Erdos91.TwoDistanceCapAndSixNonunique
open EnergyLevels91 (energy centroid)

/-- **Universal Non-Centroid Vertex Existence (`∀ S`):**
every planar configuration `S` of cardinality `2 ≤ S.card` contains a vertex `p ∈ S`
distinct from `centroid S`. -/
theorem exists_mem_ne_centroid_of_two_le_card (S : Finset Plane) (hS : 2 ≤ S.card) :
    ∃ p ∈ S, centroid S ≠ p := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  by_cases hc : centroid S = p₁
  · exact ⟨p₂, hp₂, fun h => hne (hc.symm.trans h)⟩
  · exact ⟨p₁, hp₁, hc⟩

/-- **Universal Distance-Count × Energy-Level-Count Product Bound (`∀ S`):**
for every planar configuration `S` with `2 ≤ S.card`,
`S.card - 1 ≤ 2 * distinctDistances S * energyLevelCount S`. -/
theorem card_sub_one_le_two_mul_distinctDistances_mul_energyLevelCount
    (S : Finset Plane) (hS : 2 ≤ S.card) :
    S.card - 1 ≤ 2 * distinctDistances S * energyLevelCount S := by
  obtain ⟨p, hp, hcp⟩ := exists_mem_ne_centroid_of_two_le_card S hS
  have hne : S.Nonempty := ⟨p, hp⟩
  have hbound := EnergyLevels91.energy_level_bound S (S.erase p) hne
    (Finset.erase_subset p S) p hp (Finset.notMem_erase p S) hcp
  have hcard : (S.erase p).card = S.card - 1 := Finset.card_erase_of_mem hp
  have himg : ((S.erase p).image (energy S)).card ≤ energyLevelCount S :=
    Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset p S))
  rw [hcard] at hbound
  exact hbound.trans (Nat.mul_le_mul_left (2 * distinctDistances S) himg)

/-- **Universal Iso-Energetic / Cocircular Cardinality Cap (`∀ S`):**
every planar configuration `S` with `energyLevelCount S ≤ 1` satisfies
`S.card ≤ 2 * distinctDistances S + 1`, and in particular any iso-energetic
3-distance configuration (`distinctDistances S ≤ 3`) has at most `7` points (`S.card ≤ 7`). -/
theorem iso_energetic_card_le_two_mul_distinctDistances_add_one
    (S : Finset Plane) (hlvl : energyLevelCount S ≤ 1) :
    S.card ≤ 2 * distinctDistances S + 1 ∧
      (distinctDistances S ≤ 3 → S.card ≤ 7) := by
  have h1 : S.card ≤ 2 * distinctDistances S + 1 := by
    by_cases hS : 2 ≤ S.card
    · have hb := card_sub_one_le_two_mul_distinctDistances_mul_energyLevelCount S hS
      have hmul : 2 * distinctDistances S * energyLevelCount S ≤ 2 * distinctDistances S * 1 :=
        Nat.mul_le_mul_left (2 * distinctDistances S) hlvl
      omega
    · omega
  exact ⟨h1, fun _ => by omega⟩

/-- **Universal 3-Distance Multi-Level & Cocircular Nonsimilarity Theorem for `8 ≤ S.card` (`∀ S`):**
every 3-distance planar configuration `S` (`distinctDistances S ≤ 3`) of `8 ≤ S.card` points
has at least `2` distinct vertex-energy levels (`2 ≤ energyLevelCount S`) and is nonsimilar
to every iso-energetic / regular-polygon configuration `C` (`energyLevelCount C = 1`). -/
theorem two_le_energyLevelCount_of_three_distances_of_eight_le_card
    (S : Finset Plane) (h3 : distinctDistances S ≤ 3) (hcard : 8 ≤ S.card) :
    2 ≤ energyLevelCount S ∧
      (∀ C : Finset Plane, energyLevelCount C = 1 → ¬ DilationEquivSimilar S C) := by
  have h2 : 2 ≤ energyLevelCount S := by
    by_contra hlt
    have hle1 : energyLevelCount S ≤ 1 := by omega
    have h7 := (iso_energetic_card_le_two_mul_distinctDistances_add_one S hle1).2 h3
    omega
  refine ⟨h2, ?_⟩
  intro C hC hsim
  have heq := energyLevelCount_eq_of_similar S C hsim
  omega

/-- **Universal Diameter-Equilateral Obstruction (`∀ S a b u v`):**
for any diameter pair `(a, b)` of `S` (`a ≠ b`, `∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b`),
`S` cannot contain two distinct vertices `u ≠ v` both forming equilateral triangles of
side `dist a b` with `(a, b)`. -/
theorem no_two_equilateral_over_diameter_pair
    (S : Finset Plane) (a b u v : Plane)
    (ha : a ∈ S) (hb : b ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hab : a ≠ b) (huv : u ≠ v)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hua : dist u a = dist a b) (hub : dist u b = dist a b)
    (hva : dist v a = dist a b) (hvb : dist v b = dist a b) : False := by
  have _ := ha
  have _ := hb
  have hcm := cmPoly_dist_sq_eq_zero a b u v
  rw [dist_comm a u, hua, dist_comm a v, hva, dist_comm b u, hub, dist_comm b v, hvb] at hcm
  unfold cmPoly at hcm
  have hd_pos : 0 < dist a b := dist_pos.mpr hab
  have hs_pos : 0 < dist u v := dist_pos.mpr huv
  have hd2_pos : 0 < dist a b ^ 2 := sq_pos_of_pos hd_pos
  have hs2_pos : 0 < dist u v ^ 2 := sq_pos_of_pos hs_pos
  have hle : dist u v ≤ dist a b := hdiam u hu v hv
  have hsq_le : dist u v ^ 2 ≤ dist a b ^ 2 := by
    nlinarith [dist_nonneg (x := u) (y := v), dist_nonneg (x := a) (y := b)]
  have hrel : dist a b ^ 2 * dist u v ^ 2 * (3 * dist a b ^ 2 - dist u v ^ 2) = 0 := by
    linear_combination hcm
  rcases mul_eq_zero.mp hrel with h0 | h3
  · rcases mul_eq_zero.mp h0 with hda | hdu
    · linarith
    · linarith
  · linarith

/-- **Universal Diameter-Equilateral Fiber Bound (`∀ S a b`):**
for any diameter pair `(a, b)` of `S`, at most one vertex `v ∈ S` has
`dist v a = dist a b` and `dist v b = dist a b`. -/
theorem diameter_equilateral_fiber_card_le_one
    (S : Finset Plane) (a b : Plane)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b) :
    (S.filter (fun v => dist v a = dist a b ∧ dist v b = dist a b)).card ≤ 1 := by
  by_contra hgt
  have hlt : 1 < (S.filter (fun v => dist v a = dist a b ∧ dist v b = dist a b)).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hlt
  obtain ⟨huS, hua, hub⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, hva, hvb⟩ := Finset.mem_filter.mp hv
  exact no_two_equilateral_over_diameter_pair S a b u v ha hb huS hvS hab huv hdiam hua hub hva hvb

end Erdos91.ThreeDistanceLevelAndDiameterFiberBounds


/-! ## Suite 2: Universal `k`-Deletion Score Invariant `multiDelScore` and Distance-Complete Core `k`-Deletion Multiplicity (`∀ C P D d K`) -/

namespace Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91 Erdos91.DistanceCompleteCoreDeletionInvariance Erdos91.PairDeletionInvariantsAndMultiplicity Erdos91.ExactGridEnergyAndDeletionFamilies Erdos91.ThreeUniqueMinimizer Erdos91.UnconditionalNaturalDensityOne
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Ambient `k`-deletion score `multiDelScore P D = 2 * (∑ u ∈ D, energy P u) - pairEnergy D`. -/
noncomputable def multiDelScore (P D : Finset Plane) : ℝ :=
  2 * (∑ u ∈ D, energy P u) - pairEnergy D

/-- **Universal `k`-Deletion Cross-Energy Decomposition (`∀ P D`):**
for any subset `D ⊆ P`, `∑ u ∈ D, energy (P \ D) u = (∑ u ∈ D, energy P u) - pairEnergy D`. -/
theorem sum_energy_sdiff_eq (P D : Finset Plane) (hDP : D ⊆ P) :
    (∑ u ∈ D, energy (P \ D) u) = (∑ u ∈ D, energy P u) - pairEnergy D := by
  have hsplit : ∀ u ∈ D, energy P u = energy D u + energy (P \ D) u := by
    intro u _
    unfold energy
    conv_lhs => rw [← Finset.union_sdiff_of_subset hDP]
    exact Finset.sum_union disjoint_sdiff_self_right
  have hsum : (∑ u ∈ D, energy P u) = pairEnergy D + ∑ u ∈ D, energy (P \ D) u := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    rfl
  linarith

/-- **Universal `k`-Deletion Pair-Energy Identity (`∀ P D`):**
for any subset `D ⊆ P`, `pairEnergy (P \ D) = pairEnergy P - multiDelScore P D`. -/
theorem pairEnergy_sdiff_eq_sub_multiDelScore (P D : Finset Plane) (hDP : D ⊆ P) :
    pairEnergy (P \ D) = pairEnergy P - multiDelScore P D := by
  have hunion := Erdos91.MultiSiteReplacement.pairEnergy_union_disjoint
    D (P \ D) disjoint_sdiff_self_right
  rw [Finset.union_sdiff_of_subset hDP] at hunion
  have hcross := sum_energy_sdiff_eq P D hDP
  unfold multiDelScore
  linarith

/-- **Universal `k`-Deletion Pair-Energy Difference Identity (`∀ P D₁ D₂`):**
for any `D₁ ⊆ P` and `D₂ ⊆ P`,
`pairEnergy (P \ D₁) - pairEnergy (P \ D₂) = multiDelScore P D₂ - multiDelScore P D₁`. -/
theorem pairEnergy_sdiff_sub_eq_multiDelScore_sub (P D₁ D₂ : Finset Plane)
    (hD₁ : D₁ ⊆ P) (hD₂ : D₂ ⊆ P) :
    pairEnergy (P \ D₁) - pairEnergy (P \ D₂) =
      multiDelScore P D₂ - multiDelScore P D₁ := by
  rw [pairEnergy_sdiff_eq_sub_multiDelScore P D₁ hD₁,
    pairEnergy_sdiff_eq_sub_multiDelScore P D₂ hD₂]
  ring

/-- **Universal Singleton and Pair Specialization of `multiDelScore` (`∀ P u v`):**
for any `P : Finset Plane` and distinct `u, v : Plane`,
`multiDelScore P {u} = 2 * energy P u` and `multiDelScore P {u, v} = 2 * pairDelScore P u v`. -/
theorem multiDelScore_singleton_and_pair_eq (P : Finset Plane) (u v : Plane) (huv : u ≠ v) :
    multiDelScore P {u} = 2 * energy P u ∧
      multiDelScore P {u, v} = 2 * pairDelScore P u v := by
  constructor
  · unfold multiDelScore pairEnergy
    simp [dist_self]
  · unfold multiDelScore pairDelScore pairEnergy
    rw [Finset.sum_pair huv, Finset.sum_pair huv, Finset.sum_pair huv, Finset.sum_pair huv]
    simp only [dist_self, sq, mul_zero, zero_add, add_zero]
    have hcomm : dist v u = dist u v := dist_comm v u
    rw [hcomm]
    ring

/-- **Universal Shared-Diameter `k`-Deletion Nonsimilarity Criterion (`∀ P D₁ D₂ a b`):**
if `(a, b)` is a diameter pair of `P` and `D₁, D₂ ⊆ P` avoid `a` and `b` with
`multiDelScore P D₁ ≠ multiDelScore P D₂`, then `P \ D₁` and `P \ D₂` are nonsimilar
under all full-plane similarities. -/
theorem nonsimilar_sdiff_of_multiDelScore_ne
    (P D₁ D₂ : Finset Plane) (a b : Plane) (hab : a ≠ b)
    (ha : a ∈ P) (hb : b ∈ P)
    (hD₁ : D₁ ⊆ P) (hD₂ : D₂ ⊆ P)
    (ha₁ : a ∉ D₁) (hb₁ : b ∉ D₁)
    (ha₂ : a ∉ D₂) (hb₂ : b ∉ D₂)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist a b)
    (hne : multiDelScore P D₁ ≠ multiDelScore P D₂) :
    ¬ DilationEquivSimilar (P \ D₁) (P \ D₂) := by
  intro hsim
  obtain ⟨f, hf⟩ := (similar_iff_image _ _).mp hsim
  have ha_mem₁ : a ∈ P \ D₁ := Finset.mem_sdiff.mpr ⟨ha, ha₁⟩
  have hb_mem₁ : b ∈ P \ D₁ := Finset.mem_sdiff.mpr ⟨hb, hb₁⟩
  have ha_mem₂ : a ∈ P \ D₂ := Finset.mem_sdiff.mpr ⟨ha, ha₂⟩
  have hb_mem₂ : b ∈ P \ D₂ := Finset.mem_sdiff.mpr ⟨hb, hb₂⟩
  have hpe := SimilarityEnergy91.pairEnergy_eq_of_shared_diameter (P \ D₁) (P \ D₂) f hf a b hab
    ha_mem₁ hb_mem₁ ha_mem₂ hb_mem₂
    (fun x hx y hy => hdiam x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy))
    (fun x hx y hy => hdiam x (Finset.sdiff_subset hx) y (Finset.sdiff_subset hy))
  have hdiff := pairEnergy_sdiff_sub_eq_multiDelScore_sub P D₁ D₂ hD₁ hD₂
  rw [hpe, sub_self] at hdiff
  apply hne
  linarith

/-- **Universal Distance-Complete Core `k`-Deletion Family Theorem (`∀ C P F a b d K`):**
if `C` is a distance-complete core of `P` containing diameter pair `(a, b)`, and `F` is a
finite family of `d`-element subsets `D ⊆ P` disjoint from `C` with
`K ≤ (F.image (multiDelScore P)).card`, then there exists a family `G` of `K` pairwise
nonsimilar `(P.card - d)`-point `d`-deletions of `P`, all preserving `distanceSet P` and
`distinctDistances P` (and certifying `HasAtLeastKNonsimilarMinimizers K (P.card - d)`
whenever `distinctDistances P ≤ d(P.card - d)`). -/
theorem distance_complete_core_sdiff_family_of_le_card_image_multiDelScore
    (C P : Finset Plane) (F : Finset (Finset Plane)) (a b : Plane) (d K : ℕ)
    (hC : IsDistanceCompleteCore C P) (hab : a ≠ b) (haC : a ∈ C) (hbC : b ∈ C)
    (hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist a b)
    (hF : ∀ D ∈ F, D ⊆ P ∧ Disjoint D C ∧ D.card = d)
    (hK : K ≤ (F.image (multiDelScore P)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = P.card - d ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
        distinctDistances A = distinctDistances P) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances P ≤ minimalDistinctDistances (P.card - d) →
      HasAtLeastKNonsimilarMinimizers K (P.card - d)) := by
  obtain ⟨U0, hU0_sub, hU0_card, hU0_inj⟩ :=
    exists_rep_subset_card_eq_image F (multiDelScore P)
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq (s := U0) (by omega : K ≤ U0.card)
  have hUF : U ⊆ F := hU_sub.trans hU0_sub
  let g : Finset Plane → Finset Plane := fun D => P \ D
  have haP : a ∈ P := hC.1 haC
  have hbP : b ∈ P := hC.1 hbC
  have hns : ∀ D₁ ∈ U, ∀ D₂ ∈ U, D₁ ≠ D₂ → ¬ DilationEquivSimilar (g D₁) (g D₂) := by
    intro D₁ hD₁ D₂ hD₂ hneD
    obtain ⟨hD₁P, hD₁C, _⟩ := hF D₁ (hUF hD₁)
    obtain ⟨hD₂P, hD₂C, _⟩ := hF D₂ (hUF hD₂)
    have hne_score := hU0_inj D₁ (hU_sub hD₁) D₂ (hU_sub hD₂) hneD
    exact nonsimilar_sdiff_of_multiDelScore_ne P D₁ D₂ a b hab haP hbP hD₁P hD₂P
      (Finset.disjoint_right.mp hD₁C haC) (Finset.disjoint_right.mp hD₁C hbC)
      (Finset.disjoint_right.mp hD₂C haC) (Finset.disjoint_right.mp hD₂C hbC)
      hdiam hne_score
  have hg_inj : Set.InjOn g (U : Set (Finset Plane)) := by
    intro D₁ hD₁ D₂ hD₂ heq
    by_contra hneD
    apply hns D₁ hD₁ D₂ hD₂ hneD
    rw [heq]
    exact similar_refl (g D₂)
  have hG_card : (U.image g).card = K := by
    rw [Finset.card_image_of_injOn hg_inj, hU_card]
  have hG_props : ∀ A ∈ U.image g, A.card = P.card - d ∧
      Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet P ∧
      distinctDistances A = distinctDistances P := by
    intro A hA
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hDP, hDC, hDcard⟩ := hF D (hUF hD)
    obtain ⟨hDS, hdist⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore C P D hC hDC
    have hcard : (P \ D).card = P.card - d := by
      rw [Finset.card_sdiff_of_subset hDP, hDcard]
    exact ⟨hcard, hDS, hdist⟩
  have hG_ns : ∀ A ∈ U.image g, ∀ B ∈ U.image g, A ≠ B → ¬ DilationEquivSimilar A B := by
    intro A hA B hB hAB
    obtain ⟨D₁, hD₁, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨D₂, hD₂, rfl⟩ := Finset.mem_image.mp hB
    exact hns D₁ hD₁ D₂ hD₂ (fun h => hAB (congrArg g h))
  refine ⟨⟨U.image g, hG_card, hG_props, hG_ns⟩, ?_⟩
  intro hmin
  refine ⟨U.image g, hG_card, ?_, hG_ns⟩
  intro A hA
  obtain ⟨hcard, _, hdist⟩ := hG_props A hA
  have hlo := minimal_le A (P.card - d) hcard
  exact ⟨hcard, by omega⟩

end Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity


/-! ## Suite 3: Universal Integer-Lattice `hexCoordMultiDelScore` Bridge and Patch `k`-Deletion Theorems (`∀ L R d K`) -/

namespace Erdos91.LatticeMultiDeletionScoreAndPatchFamilies
open Finset Minimizer91 PlateauDefinitions91 Erdos91.DistanceCompleteCoreDeletionInvariance Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity Erdos91.EquilateralTriangularPatchCoreAndPairDeletions Erdos91.HexagonalPatchRightCoreAndPairDeletions Erdos91.TruncatedTriangleAndEquilateralPatchFamilies Erdos91.TriangularLatticeHexagonAndSub130Majority Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions Erdos91.UnconditionalNaturalDensityOne Erdos91.ThreeUniqueMinimizer
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Exact integer lattice internal pair energy `∑ p ∈ D_coords, ∑ q ∈ D_coords, triNormSq (triOffset p q)`. -/
def hexCoordPairEnergy (D_coords : Finset (ℕ × ℕ)) : ℕ :=
  D_coords.sum (fun p => D_coords.sum (fun q => triNormSq (triOffset p q)))

/-- Exact integer lattice `k`-deletion score `2 * (∑ p ∈ D_coords, hexCoordEnergy k c m p) - hexCoordPairEnergy D_coords`. -/
def hexCoordMultiDelScore (k c m : ℕ) (D_coords : Finset (ℕ × ℕ)) : ℕ :=
  2 * (D_coords.sum (hexCoordEnergy k c m)) - hexCoordPairEnergy D_coords

open scoped Classical

/-- **Universal Integer-Lattice Subset Pair-Energy Identity (`∀ D_coords`):**
for any `D_coords : Finset (ℕ × ℕ)`, `pairEnergy (D_coords.image triPoint) = (hexCoordPairEnergy D_coords : ℝ)`. -/
theorem pairEnergy_image_triPoint_eq_hexCoordPairEnergy (D_coords : Finset (ℕ × ℕ)) :
    pairEnergy (D_coords.image triPoint) = ((hexCoordPairEnergy D_coords : ℕ) : ℝ) := by
  unfold pairEnergy hexCoordPairEnergy
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h)]
  push_cast
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact dist_triPoint_sq_eq_triNormSq p q

/-- **Universal Lattice Subset Pair-Energy Domination (`∀ k c m D_coords`):**
for any `D_coords ⊆ hexCoords k c m`, `hexCoordPairEnergy D_coords ≤ D_coords.sum (hexCoordEnergy k c m)`. -/
theorem hexCoordPairEnergy_le_sum_hexCoordEnergy (k c m : ℕ)
    {D_coords : Finset (ℕ × ℕ)} (hD : D_coords ⊆ hexCoords k c m) :
    hexCoordPairEnergy D_coords ≤ D_coords.sum (hexCoordEnergy k c m) ∧
      hexCoordPairEnergy D_coords ≤ 2 * D_coords.sum (hexCoordEnergy k c m) := by
  have hle : hexCoordPairEnergy D_coords ≤ D_coords.sum (hexCoordEnergy k c m) := by
    unfold hexCoordPairEnergy hexCoordEnergy
    refine Finset.sum_le_sum (fun p _ => ?_)
    exact Finset.sum_le_sum_of_subset hD
  exact ⟨hle, by omega⟩

/-- **Universal Integer-Lattice `k`-Deletion Score Identity (`∀ k c m D_coords`):**
for any `D_coords ⊆ hexCoords k c m`, `D_coords.image triPoint ⊆ hexSet k c m` and
`multiDelScore (hexSet k c m) (D_coords.image triPoint) = (hexCoordMultiDelScore k c m D_coords : ℝ)`. -/
theorem multiDelScore_hexSet_eq_hexCoordMultiDelScore (k c m : ℕ)
    {D_coords : Finset (ℕ × ℕ)} (hD : D_coords ⊆ hexCoords k c m) :
    D_coords.image triPoint ⊆ hexSet k c m ∧
      multiDelScore (hexSet k c m) (D_coords.image triPoint) =
        ((hexCoordMultiDelScore k c m D_coords : ℕ) : ℝ) := by
  refine ⟨Finset.image_subset_image hD, ?_⟩
  unfold multiDelScore hexCoordMultiDelScore
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h),
    pairEnergy_image_triPoint_eq_hexCoordPairEnergy]
  have hsum : (∑ u ∈ D_coords, energy (hexSet k c m) (triPoint u)) =
      ((D_coords.sum (hexCoordEnergy k c m) : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun p _ => energy_hexSet_eq_hexCoordEnergy k c m p)
  rw [hsum]
  have hle := (hexCoordPairEnergy_le_sum_hexCoordEnergy k c m hD).2
  push_cast [hle]
  rfl

/-- **Universal Membership Characterization for `(P_coords \ C_coords).powersetCard d` (`∀ P_coords C_coords D_coords d`):**
every `D_coords ∈ (P_coords \ C_coords).powersetCard d` satisfies `D_coords ⊆ P_coords`,
`Disjoint D_coords C_coords`, and `D_coords.card = d`. -/
theorem mem_powersetCard_sdiff_props {P_coords C_coords D_coords : Finset (ℕ × ℕ)} {d : ℕ}
    (hD : D_coords ∈ (P_coords \ C_coords).powersetCard d) :
    D_coords ⊆ P_coords ∧ Disjoint D_coords C_coords ∧ D_coords.card = d := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hD
  refine ⟨hsub.trans Finset.sdiff_subset, ?_, hcard⟩
  exact Finset.disjoint_left.mpr (fun x hx => (Finset.mem_sdiff.mp (hsub hx)).2)

/-- **Universal Coordinate-Level `k`-Deletion Family Theorem on `hexSet k c m` (`∀ k c m d K`):**
for any `k ≤ m + 1` (`m ≥ 1`), any distance-complete coordinate core `C_coords ⊆ hexCoords k c m`,
any diameter pair `a_c, b_c ∈ C_coords` with `triNormSq (triOffset a_c b_c) = 4 * m * m`, and
any finite family `F_coords` of `d`-element subsets of `hexCoords k c m` disjoint from `C_coords`
with `K ≤ (F_coords.image (hexCoordMultiDelScore k c m)).card`, there exist `K` pairwise nonsimilar
`((hexSet k c m).card - d)`-point `d`-deletions of `hexSet k c m` preserving `distanceSet (hexSet k c m)`. -/
theorem hexSet_multi_deletion_family_of_coord_core
    (k c m d K : ℕ) (hkm : k ≤ m + 1) (hm : 1 ≤ m)
    (C_coords : Finset (ℕ × ℕ)) (F_coords : Finset (Finset (ℕ × ℕ)))
    (a_c b_c : ℕ × ℕ)
    (hCore : IsDistanceCompleteCore (C_coords.image triPoint) (hexSet k c m))
    (ha_c : a_c ∈ C_coords) (hb_c : b_c ∈ C_coords)
    (hdiam_norm : triNormSq (triOffset a_c b_c) = 4 * m * m)
    (hF : ∀ D_c ∈ F_coords, D_c ⊆ hexCoords k c m ∧ Disjoint D_c C_coords ∧ D_c.card = d)
    (hK : K ≤ (F_coords.image (hexCoordMultiDelScore k c m)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (hexSet k c m).card - d ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet k c m) ∧
        distinctDistances A = distinctDistances (hexSet k c m)) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances (hexSet k c m) ≤ minimalDistinctDistances ((hexSet k c m).card - d) →
      HasAtLeastKNonsimilarMinimizers K ((hexSet k c m).card - d)) := by
  let C := C_coords.image triPoint
  let P := hexSet k c m
  let mapSet : Finset (ℕ × ℕ) → Finset Plane := fun D_c => D_c.image triPoint
  let F := F_coords.image mapSet
  have hab : triPoint a_c ≠ triPoint b_c := by
    intro heq
    have h0 : a_c = b_c := triPoint_injective heq
    subst h0
    have hzero : triNormSq (triOffset a_c a_c) = 0 := by
      unfold triOffset triNormSq
      simp [Nat.dist_self]
    have hpos : 0 < 4 * m * m := by positivity
    omega
  have haC : triPoint a_c ∈ C := Finset.mem_image_of_mem triPoint ha_c
  have hbC : triPoint b_c ∈ C := Finset.mem_image_of_mem triPoint hb_c
  have hdiam_sq : dist (triPoint a_c) (triPoint b_c) ^ 2 = ((4 * m * m : ℕ) : ℝ) := by
    rw [dist_triPoint_sq_eq_triNormSq, hdiam_norm]
  have hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist (triPoint a_c) (triPoint b_c) :=
    fun x hx y hy => dist_le_of_mem_hexSet_of_dist_sq_eq k c m hkm _ _ hdiam_sq hx hy
  have hF_plane : ∀ D ∈ F, D ⊆ P ∧ Disjoint D C ∧ D.card = d := by
    intro D hD
    obtain ⟨D_c, hD_c, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hsub, hdisj, hcard⟩ := hF D_c hD_c
    refine ⟨Finset.image_subset_image hsub, ?_, ?_⟩
    · refine Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_)
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hx2
      exact Finset.disjoint_left.mp hdisj hp (triPoint_injective heq ▸ hq)
    · rw [Finset.card_image_of_injective _ triPoint_injective, hcard]
  have himg_eq : F.image (multiDelScore P) =
      (F_coords.image (hexCoordMultiDelScore k c m)).image (fun s : ℕ => (s : ℝ)) := by
    ext y
    simp only [F, mapSet, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨D_c, hD_c, rfl⟩, rfl⟩
      have hsub := (hF D_c hD_c).1
      exact ⟨hexCoordMultiDelScore k c m D_c, ⟨D_c, hD_c, rfl⟩,
        (multiDelScore_hexSet_eq_hexCoordMultiDelScore k c m hsub).2.symm⟩
    · rintro ⟨s, ⟨D_c, hD_c, rfl⟩, rfl⟩
      have hsub := (hF D_c hD_c).1
      exact ⟨D_c.image triPoint, ⟨D_c, hD_c, rfl⟩,
        (multiDelScore_hexSet_eq_hexCoordMultiDelScore k c m hsub).2⟩
  have hK_plane : K ≤ (F.image (multiDelScore P)).card := by
    rw [himg_eq, Finset.card_image_of_injective _ Nat.cast_injective]
    exact hK
  exact distance_complete_core_sdiff_family_of_le_card_image_multiDelScore
    C P F (triPoint a_c) (triPoint b_c) d K hCore hab haC hbC hdiam hF_plane hK_plane

/-- **Universal `k`-Deletion Family Theorem on Equilateral Triangular Patches `T_L = triPatchSet L` (`∀ L ≥ 2, ∀ d K`):**
for any `L ≥ 2`, `d : ℕ`, and `K ≤ (((triPatchCoords L \ triPatchCoreCoords L).powersetCard d).image (hexCoordMultiDelScore L 0 (L - 1))).card`,
there exist `K` pairwise nonsimilar `((triPatchSet L).card - d)`-point `d`-deletions of `triPatchSet L`
preserving the exact distance set `(triUtp (L - 1)).image triNorm`. -/
theorem triPatchSet_multi_deletion_family_of_le_card_image
    (L d K : ℕ) (hL : 2 ≤ L)
    (hK : K ≤ (((triPatchCoords L \ triPatchCoreCoords L).powersetCard d).image
      (hexCoordMultiDelScore L 0 (L - 1))).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (triPatchSet L).card - d ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp (L - 1)).image triNorm ∧
        distinctDistances A = ((triUtp (L - 1)).image triNormSq).card) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (((triUtp (L - 1)).image triNormSq).card ≤ minimalDistinctDistances ((triPatchSet L).card - d) →
      HasAtLeastKNonsimilarMinimizers K ((triPatchSet L).card - d)) := by
  obtain ⟨_, hDS, hdd, hCore⟩ := distanceSet_triPatchCore_eq_and_isDistanceCompleteCore L (by omega)
  change Erdos91.DistanceErasure.distanceSet (hexSet L 0 (L - 1)) = (triUtp (L - 1)).image triNorm at hDS
  change distinctDistances (hexSet L 0 (L - 1)) = ((triUtp (L - 1)).image triNormSq).card at hdd
  have ha_c : (0, 0) ∈ triPatchCoreCoords L := by
    unfold triPatchCoreCoords
    exact Finset.mem_insert_self (0, 0) (triUtp (L - 1))
  have hb_c : (0, L - 1) ∈ triPatchCoreCoords L := by
    unfold triPatchCoreCoords
    apply Finset.mem_insert_of_mem
    rw [mem_triUtp_iff]
    refine ⟨by intro h; have h2 : L - 1 = 0 := congrArg Prod.snd h; omega, by omega, by omega⟩
  have hdiam_norm : triNormSq (triOffset (0, 0) (0, L - 1)) = 4 * (L - 1) * (L - 1) := by
    have h0 : triOffset (0, 0) (0, L - 1) = (0, L - 1) := triOffset_zero_eq (by omega)
    rw [h0]
    unfold triNormSq
    ring
  have hF : ∀ D_c ∈ (triPatchCoords L \ triPatchCoreCoords L).powersetCard d,
      D_c ⊆ hexCoords L 0 (L - 1) ∧ Disjoint D_c (triPatchCoreCoords L) ∧ D_c.card = d :=
    fun _ hD => mem_powersetCard_sdiff_props hD
  have hres := hexSet_multi_deletion_family_of_coord_core
    L 0 (L - 1) d K (by omega) (by omega) (triPatchCoreCoords L)
    ((triPatchCoords L \ triPatchCoreCoords L).powersetCard d)
    (0, 0) (0, L - 1) hCore ha_c hb_c hdiam_norm hF hK
  change (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (hexSet L 0 (L - 1)).card - d ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp (L - 1)).image triNorm ∧
        distinctDistances A = ((triUtp (L - 1)).image triNormSq).card) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (((triUtp (L - 1)).image triNormSq).card ≤ minimalDistinctDistances ((hexSet L 0 (L - 1)).card - d) →
      HasAtLeastKNonsimilarMinimizers K ((hexSet L 0 (L - 1)).card - d))
  simpa only [hDS, hdd] using hres

/-- **Universal `k`-Deletion Family Theorem on Regular Hexagonal Patches `H_R = hexSet (2*R + 1) R (2*R)` (`∀ R ≥ 1, ∀ d K`):**
for any `R ≥ 1`, `d : ℕ`, and `K ≤ (((hexCoords (2*R + 1) R (2*R) \ hexRightCoreCoords R).powersetCard d).image (hexCoordMultiDelScore (2*R + 1) R (2*R))).card`,
there exist `K` pairwise nonsimilar `((hexSet (2*R + 1) R (2*R)).card - d)`-point `d`-deletions of `H_R`
preserving the exact distance set `(triUtp (2*R)).image triNorm`. -/
theorem hexSet_regular_multi_deletion_family_of_le_card_image
    (R d K : ℕ) (hR : 1 ≤ R)
    (hK : K ≤ (((hexCoords (2 * R + 1) R (2 * R) \ hexRightCoreCoords R).powersetCard d).image
      (hexCoordMultiDelScore (2 * R + 1) R (2 * R))).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = (hexSet (2 * R + 1) R (2 * R)).card - d ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp (2 * R)).image triNorm ∧
        distinctDistances A = ((triUtp (2 * R)).image triNormSq).card) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (((triUtp (2 * R)).image triNormSq).card ≤
        minimalDistinctDistances ((hexSet (2 * R + 1) R (2 * R)).card - d) →
      HasAtLeastKNonsimilarMinimizers K ((hexSet (2 * R + 1) R (2 * R)).card - d)) := by
  obtain ⟨hCore, _⟩ := hexRightCore_isDistanceCompleteCore R
  have hDS_hex : Erdos91.DistanceErasure.distanceSet (hexSet (2 * R + 1) R (2 * R)) =
      (triUtp (2 * R)).image triNorm := distanceSet_hexSet_regular_eq R
  have hdd : distinctDistances (hexSet (2 * R + 1) R (2 * R)) =
      ((triUtp (2 * R)).image triNormSq).card := distinctDistances_hexSet_regular_eq R
  have ha_c : (0, R) ∈ hexRightCoreCoords R := by
    unfold hexRightCoreCoords
    exact Finset.mem_insert_self (0, R) _
  have hb_c : (2 * R, R) ∈ hexRightCoreCoords R := by
    unfold hexRightCoreCoords
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    refine Finset.mem_image.mpr ⟨(R, R), ?_, by ext <;> dsimp <;> omega⟩
    rw [mem_triUtp_iff]
    refine ⟨by intro h; have h1 : R = 0 := congrArg Prod.fst h; omega, le_rfl, by omega⟩
  have hdiam_norm : triNormSq (triOffset (0, R) (2 * R, R)) = 4 * (2 * R) * (2 * R) := by
    have h0 : triOffset (0, R) (2 * R, R) = (0, 2 * R) := by
      unfold triOffset
      have hdx : Nat.dist 0 (2 * R) = 2 * R := by unfold Nat.dist; omega
      have hdy : Nat.dist R R = 0 := Nat.dist_self R
      dsimp
      rw [hdx, hdy]
      have hcond : (0 ≤ 2 * R ∧ R ≤ R) ∨ (2 * R ≤ 0 ∧ R ≤ R) := Or.inl ⟨Nat.zero_le _, le_rfl⟩
      have hnot : ¬ (2 * R ≤ 0) := by omega
      simp [hcond, hnot]
    rw [h0]
    unfold triNormSq
    ring
  have hF : ∀ D_c ∈ (hexCoords (2 * R + 1) R (2 * R) \ hexRightCoreCoords R).powersetCard d,
      D_c ⊆ hexCoords (2 * R + 1) R (2 * R) ∧ Disjoint D_c (hexRightCoreCoords R) ∧ D_c.card = d :=
    fun _ hD => mem_powersetCard_sdiff_props hD
  have hres := hexSet_multi_deletion_family_of_coord_core
    (2 * R + 1) R (2 * R) d K (by omega) (by omega) (hexRightCoreCoords R)
    ((hexCoords (2 * R + 1) R (2 * R) \ hexRightCoreCoords R).powersetCard d)
    (0, R) (2 * R, R) hCore ha_c hb_c hdiam_norm hF hK
  simpa only [hDS_hex, hdd] using hres

end Erdos91.LatticeMultiDeletionScoreAndPatchFamilies


/-! ## Suite 4: Exact 13-Point 6-Distance Rounded Hexagon (`d(13) ≤ 6`), Certified `k ≥ 3` Multi-Deletion Families for `n = 8..16`, and Structural Dichotomies -/

namespace Erdos91.RoundedHexagonAndCertifiedMultiDeletionFamilies
open Finset Minimizer91 PlateauDefinitions91 Erdos91.DistanceCompleteCoreDeletionInvariance Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity Erdos91.LatticeMultiDeletionScoreAndPatchFamilies Erdos91.EquilateralTriangularPatchCoreAndPairDeletions Erdos91.HexagonalPatchRightCoreAndPairDeletions Erdos91.TruncatedTriangleAndEquilateralPatchFamilies Erdos91.TriangularLatticeHexagonAndSub130Majority Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet Erdos91.HexagonCentralSymmetryEnergyAndNonsimilarDeletions Erdos91.UnconditionalNaturalDensityOne Erdos91.TwoDistanceCapAndSixNonunique
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- The 6 corner coordinates of the 19-point regular hexagonal patch `hexCoords 5 2 4`. -/
def roundedHexCorners : Finset (ℕ × ℕ) :=
  {(0, 2), (2, 0), (0, 4), (4, 0), (2, 4), (4, 2)}

/-- The 13-point rounded hexagon coordinate patch `hexCoords 5 2 4 \ roundedHexCorners`. -/
def roundedHex13Coords : Finset (ℕ × ℕ) :=
  hexCoords 5 2 4 \ roundedHexCorners

/-- 4-point distance-complete coordinate core `{(0, 3), (1, 1), (1, 3), (4, 1)}` of `roundedHex13Coords`. -/
def roundedHexCore4Coords : Finset (ℕ × ℕ) :=
  {(0, 3), (1, 1), (1, 3), (4, 1)}

/-- The 6-element triangular-lattice offset set `((triUtp 4).erase (0, 4)).erase (1, 3)`
with squared norms `{4, 12, 16, 28, 36, 48}`. -/
def roundedHexUtp6 : Finset (ℕ × ℕ) :=
  ((triUtp 4).erase (0, 4)).erase (1, 3)

/-- Planar 13-point rounded hexagon `roundedHex13 = roundedHex13Coords.image triPoint`. -/
noncomputable def roundedHex13 : Finset Plane :=
  roundedHex13Coords.image triPoint

/-- Planar 4-point distance-complete core `roundedHexCore4 = roundedHexCore4Coords.image triPoint`. -/
noncomputable def roundedHexCore4 : Finset Plane :=
  roundedHexCore4Coords.image triPoint

open scoped Classical

/-- **Exact 13-Point 6-Distance Rounded Hexagon & Core Theorem (`∀ p`):**
every `p ∈ roundedHexCore4Coords` maps into `roundedHex13`, `roundedHex13.card = 13`,
`roundedHexCore4.card = 4`, `IsDistanceCompleteCore roundedHexCore4 roundedHex13`,
`distanceSet roundedHex13 = roundedHexUtp6.image triNorm`, `distinctDistances roundedHex13 = 6`,
and consequently `minimalDistinctDistances 13 ≤ 6` (sharpening `d(13) ≤ 8` down to `6`). -/
theorem card_and_distanceSet_roundedHex13_and_core4
    (p : ℕ × ℕ) (hp : p ∈ roundedHexCore4Coords) :
    triPoint p ∈ roundedHex13 ∧
      roundedHex13.card = 13 ∧
      roundedHexCore4.card = 4 ∧
      IsDistanceCompleteCore roundedHexCore4 roundedHex13 ∧
      Erdos91.DistanceErasure.distanceSet roundedHex13 = roundedHexUtp6.image triNorm ∧
      distinctDistances roundedHex13 = 6 ∧
      minimalDistinctDistances 13 ≤ 6 := by
  have hcard13 : roundedHex13.card = 13 := by
    unfold roundedHex13
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hcard4 : roundedHexCore4.card = 4 := by
    unfold roundedHexCore4
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hsub_coords : roundedHexCore4Coords ⊆ roundedHex13Coords := by decide
  have hsub_core : roundedHexCore4 ⊆ roundedHex13 := Finset.image_subset_image hsub_coords
  have h_off : ∀ a ∈ roundedHex13Coords, ∀ b ∈ roundedHex13Coords, a ≠ b →
      triOffset a b ∈ roundedHexUtp6 := by decide
  have hupper : Erdos91.DistanceErasure.distanceSet roundedHex13 ⊆ roundedHexUtp6.image triNorm := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (Erdos91.DistanceErasure.mem_distanceSet _ _).mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg triPoint h)
    rw [dist_triPoint_eq a b]
    exact Finset.mem_image_of_mem triNorm (h_off a ha b hb hab)
  have h_edge : ∀ a b : ℕ × ℕ, a ∈ roundedHexCore4Coords → b ∈ roundedHexCore4Coords → a ≠ b →
      triNorm (triOffset a b) ∈ Erdos91.DistanceErasure.distanceSet roundedHexCore4 := by
    intro a b ha hb hab
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint a, Finset.mem_image_of_mem triPoint ha,
       triPoint b, Finset.mem_image_of_mem triPoint hb,
       fun h => hab (triPoint_injective h), dist_triPoint_eq a b⟩
  have hlower : roundedHexUtp6.image triNorm ⊆ Erdos91.DistanceErasure.distanceSet roundedHexCore4 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ roundedHexUtp6,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (1, 1) ∨ v = (1, 2) ∨ v = (2, 2) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 3) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (1, 1) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (1, 1) (4, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (1, 1) (by decide) (by decide) (by decide)
    · exact h_edge (1, 3) (4, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (4, 1) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet roundedHexCore4 = roundedHexUtp6.image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hupper) hlower
  have hDS_r13 : Erdos91.DistanceErasure.distanceSet roundedHex13 = roundedHexUtp6.image triNorm :=
    Finset.Subset.antisymm hupper (hlower.trans (distanceSet_mono hsub_core))
  have hCore : IsDistanceCompleteCore roundedHexCore4 roundedHex13 :=
    ⟨hsub_core, hDS_core.trans hDS_r13.symm⟩
  have hdd : distinctDistances roundedHex13 = 6 := by
    change (Erdos91.DistanceErasure.distanceSet roundedHex13).card = 6
    rw [hDS_r13, card_image_triNorm_eq_card_image_triNormSq]
    rfl
  have hd13 : minimalDistinctDistances 13 ≤ 6 :=
    (minimal_le roundedHex13 13 hcard13).trans hdd.le
  exact ⟨hsub_core (Finset.mem_image_of_mem triPoint hp), hcard13, hcard4, hCore, hDS_r13, hdd, hd13⟩

/-- **Universal `k`-Deletion Distance-Set Invariance and Conditional Optimality on `roundedHex13` (`∀ D d`):**
for every `D ⊆ roundedHex13` disjoint from `roundedHexCore4` with `D.card = d`,
`roundedHex13 \ D` has `13 - d` points and exact 6-element distance set `distanceSet roundedHex13`
(`minimalDistinctDistances (13 - d) ≤ 6`), and is globally optimal whenever `6 ≤ d(13 - d)`. -/
theorem roundedHex13_sdiff_distanceSet_and_optimal_of_six_le
    (D : Finset Plane) (d : ℕ) (hDP : D ⊆ roundedHex13)
    (hDC : Disjoint D roundedHexCore4) (hDcard : D.card = d) :
    (roundedHex13 \ D).card = 13 - d ∧
      Erdos91.DistanceErasure.distanceSet (roundedHex13 \ D) =
        Erdos91.DistanceErasure.distanceSet roundedHex13 ∧
      distinctDistances (roundedHex13 \ D) = 6 ∧
      minimalDistinctDistances (13 - d) ≤ 6 ∧
      (6 ≤ minimalDistinctDistances (13 - d) → IsOptimal (roundedHex13 \ D) (13 - d)) := by
  obtain ⟨_, hcard13, _, hCore, _, hdd6, _⟩ :=
    card_and_distanceSet_roundedHex13_and_core4 (0, 3) (by decide)
  obtain ⟨hDS, hdd⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore
    roundedHexCore4 roundedHex13 D hCore hDC
  have hcard : (roundedHex13 \ D).card = 13 - d := by
    rw [Finset.card_sdiff_of_subset hDP, hcard13, hDcard]
  have hdd_eq : distinctDistances (roundedHex13 \ D) = 6 := hdd.trans hdd6
  have hmin_le : minimalDistinctDistances (13 - d) ≤ 6 :=
    (minimal_le (roundedHex13 \ D) (13 - d) hcard).trans hdd_eq.le
  refine ⟨hcard, hDS, hdd_eq, hmin_le, ?_⟩
  intro h6
  exact ⟨hcard, by omega⟩

/-- **Certified 18-Configuration Triple-Deletion Family at `n = 12` on `T_5 = triPatchSet 5` (`∀ K ≤ 18`):**
for every `K ≤ 18`, there exists a family `G` of `K` pairwise nonsimilar `12`-point
3-deletions of `triPatchSet 5 = hexSet 5 0 4` outside `triPatchCore 5`, all sharing
the exact 8-element distance set `(triUtp 4).image triNorm` (`distinctDistances A = 8`),
and if `8 ≤ d(12)` then `HasAtLeastKNonsimilarMinimizers K 12`. -/
theorem triPatchSet_5_twelve_point_triple_deletion_family (K : ℕ) (hK : K ≤ 18) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = 12 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (8 ≤ minimalDistinctDistances 12 → HasAtLeastKNonsimilarMinimizers K 12) := by
  have hcard15 : (triPatchSet 5).card = 15 := by
    unfold triPatchSet; rw [card_hexSet]; rfl
  have hdd8 : ((triUtp 4).image triNormSq).card = 8 := rfl
  have hres := triPatchSet_multi_deletion_family_of_le_card_image 5 3 K (by omega) (hK.trans_eq rfl)
  simpa only [hcard15, hdd8] using hres

/-- **Certified 15-Configuration 4-Deletion (`n = 11`) and 6-Configuration 5-Deletion (`n = 10`) Families on `T_5` (`∀ K₁ ≤ 15, ∀ K₂ ≤ 6`):**
for every `K₁ ≤ 15` and `K₂ ≤ 6`, `triPatchSet 5 = hexSet 5 0 4` admits `K₁` pairwise
nonsimilar `11`-point 4-deletions and `K₂` pairwise nonsimilar `10`-point 5-deletions
outside `triPatchCore 5`, all preserving the 8-element distance set `(triUtp 4).image triNorm`. -/
theorem triPatchSet_5_eleven_and_ten_point_multi_deletion_families
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 15) (hK₂ : K₂ ≤ 6) :
    (∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 11 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 10 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) := by
  have hcard15 : (triPatchSet 5).card = 15 := by
    unfold triPatchSet; rw [card_hexSet]; rfl
  have hdd8 : ((triUtp 4).image triNormSq).card = 8 := rfl
  have hres4 := (triPatchSet_multi_deletion_family_of_le_card_image 5 4 K₁ (by omega) (hK₁.trans_eq rfl)).1
  have hres5 := (triPatchSet_multi_deletion_family_of_le_card_image 5 5 K₂ (by omega) (hK₂.trans_eq rfl)).1
  exact ⟨by simpa only [hcard15, hdd8] using hres4, by simpa only [hcard15, hdd8] using hres5⟩

/-- **Certified 21-Configuration 3-Deletion (`n = 9`) and 28-Configuration 4-Deletion (`n = 8`) Families on `hexSet 4 1 3` (`∀ K₁ ≤ 21, ∀ K₂ ≤ 28`):**
for every `K₁ ≤ 21` and `K₂ ≤ 28`, the 12-point truncated triangle `hexSet 4 1 3` admits
`K₁` pairwise nonsimilar `9`-point 3-deletions and `K₂` pairwise nonsimilar `8`-point
4-deletions outside `truncTriCore4`, all preserving the 5-element distance set `distanceSet (hexSet 4 1 3)`. -/
theorem hexSet_4_1_3_nine_and_eight_point_multi_deletion_families
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 21) (hK₂ : K₂ ≤ 28) :
    (∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 9 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ∧
        distinctDistances A = 5) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 8 ∧
        Erdos91.DistanceErasure.distanceSet A = Erdos91.DistanceErasure.distanceSet (hexSet 4 1 3) ∧
        distinctDistances A = 5) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) := by
  obtain ⟨_, hcard12, _, hCore, _, hdd5⟩ :=
    card_and_distanceSet_hexSet_4_1_3_and_truncTriCore4 (0, 1) (by decide)
  have hF3 : ∀ D_c ∈ (hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 3,
      D_c ⊆ hexCoords 4 1 3 ∧ Disjoint D_c truncTriCore4Coords ∧ D_c.card = 3 :=
    fun _ hD => mem_powersetCard_sdiff_props hD
  have hF4 : ∀ D_c ∈ (hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 4,
      D_c ⊆ hexCoords 4 1 3 ∧ Disjoint D_c truncTriCore4Coords ∧ D_c.card = 4 :=
    fun _ hD => mem_powersetCard_sdiff_props hD
  have himg3 : (((hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 3).image
      (hexCoordMultiDelScore 4 1 3)).card = 21 := rfl
  have himg4 : (((hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 4).image
      (hexCoordMultiDelScore 4 1 3)).card = 28 := rfl
  have hres3 := (hexSet_multi_deletion_family_of_coord_core
    4 1 3 3 K₁ (by omega) (by omega) truncTriCore4Coords
    ((hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 3)
    (0, 1) (3, 1) hCore (by decide) (by decide) rfl hF3 (by omega)).1
  have hres4 := (hexSet_multi_deletion_family_of_coord_core
    4 1 3 4 K₂ (by omega) (by omega) truncTriCore4Coords
    ((hexCoords 4 1 3 \ truncTriCore4Coords).powersetCard 4)
    (0, 1) (3, 1) hCore (by decide) (by decide) rfl hF4 (by omega)).1
  exact ⟨by simpa only [hcard12, hdd5] using hres3, by simpa only [hcard12, hdd5] using hres4⟩

/-- **Certified 29-Configuration 3-Deletion (`n = 16`) and 20-Configuration 7-Deletion (`n = 12`) Families on `H_2 = hexSet 5 2 4` (`∀ K₁ ≤ 29, ∀ K₂ ≤ 20`):**
for every `K₁ ≤ 29` and `K₂ ≤ 20`, the 19-point regular hexagon `hexSet 5 2 4` admits
`K₁` pairwise nonsimilar `16`-point 3-deletions and `K₂` pairwise nonsimilar `12`-point
7-deletions outside `hexRightCore 2`, all preserving the 8-element distance set `(triUtp 4).image triNorm`. -/
theorem hexSet_5_2_4_sixteen_and_twelve_point_multi_deletion_families
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 29) (hK₂ : K₂ ≤ 20) :
    (∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 16 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 12 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) := by
  have hcard19 : (hexSet 5 2 4).card = 19 := Erdos91.ExactHexagonDistanceCountsR1To18.card_hexSet_regular_2
  have hdd8 : ((triUtp 4).image triNormSq).card = 8 := rfl
  have hres3 := (hexSet_regular_multi_deletion_family_of_le_card_image 2 3 K₁ (by omega) (hK₁.trans_eq rfl)).1
  have hres7 := (hexSet_regular_multi_deletion_family_of_le_card_image 2 7 K₂ (by omega) (hK₂.trans_eq rfl)).1
  exact ⟨by simpa only [hcard19, hdd8] using hres3, by simpa only [hcard19, hdd8] using hres7⟩

/-- **Unconditional `n = 8, 9, 10, 11, 12, 13` Structural Synthesis & Plateau Dichotomy (`∀ K₁ ≤ 12, ∀ K₂ ≤ 3`):**
combining `d(7) = 3`, `d(12) ≤ 5` (`hexSet 4 1 3`), and `d(13) ≤ 6` (`roundedHex13`),
at least one of the following holds unconditionally:
1. `d(12) = d(13) ≤ 5` and `¬ UniqueMinimizer 12`,
2. `d(12) = 5 ∧ d(13) = 6` and (`HasAtLeastKNonsimilarMinimizers K₁ 10 ∧ HasAtLeastKNonsimilarMinimizers K₂ 11`
   or `HasAtLeastKNonsimilarMinimizers K₂ 11` or `¬ UniqueMinimizer 10` or `¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9`),
3. `d(12) ≤ 4 ∧ d(13) ≤ 6` and (`¬ UniqueMinimizer 11` or `¬ UniqueMinimizer 10` or (`¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9`)). -/
theorem unconditional_twelve_thirteen_plateau_or_step_six_dichotomy
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 12) (hK₂ : K₂ ≤ 3) :
    (minimalDistinctDistances 12 = minimalDistinctDistances 13 ∧
      minimalDistinctDistances 12 ≤ 5 ∧ ¬ UniqueMinimizer 12) ∨
    (minimalDistinctDistances 12 = 5 ∧ minimalDistinctDistances 13 = 6 ∧
      ((HasAtLeastKNonsimilarMinimizers K₁ 10 ∧ HasAtLeastKNonsimilarMinimizers K₂ 11) ∨
        HasAtLeastKNonsimilarMinimizers K₂ 11 ∨ ¬ UniqueMinimizer 10 ∨
        (¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9))) ∨
    (minimalDistinctDistances 12 ≤ 4 ∧ minimalDistinctDistances 13 ≤ 6 ∧
      (¬ UniqueMinimizer 11 ∨ ¬ UniqueMinimizer 10 ∨
        (¬ UniqueMinimizer 8 ∧ ¬ UniqueMinimizer 9))) := by
  have hd7 : minimalDistinctDistances 7 = 3 := minimalDistinctDistances_seven
  have hm78 := MinimumMonotone91.minimum_monotone (by omega : 7 ≤ 8)
  have hm89 := MinimumMonotone91.minimum_monotone (by omega : 8 ≤ 9)
  have hm910 := MinimumMonotone91.minimum_monotone (by omega : 9 ≤ 10)
  have hm1011 := MinimumMonotone91.minimum_monotone (by omega : 10 ≤ 11)
  have hm1112 := MinimumMonotone91.minimum_monotone (by omega : 11 ≤ 12)
  have hm1213 := MinimumMonotone91.minimum_monotone (by omega : 12 ≤ 13)
  have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
  have hd13 : minimalDistinctDistances 13 ≤ 6 :=
    (card_and_distanceSet_roundedHex13_and_core4 (0, 3) (by decide)).2.2.2.2.2.2
  by_cases hplat12 : minimalDistinctDistances 12 = minimalDistinctDistances 13
  · left
    exact ⟨hplat12, hd12,
      Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
        12 (by omega) hplat12 (by omega)⟩
  · by_cases hd12_5 : minimalDistinctDistances 12 = 5
    · right; left
      have hd13_6 : minimalDistinctDistances 13 = 6 := by omega
      refine ⟨hd12_5, hd13_6, ?_⟩
      rcases unconditional_ten_eleven_dichotomy K₁ K₂ hK₁ hK₂ with h1 | h2 | h3 | ⟨_, _, _, _, h8, h9⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr ⟨h8, h9⟩))
    · right; right
      have hd12_le4 : minimalDistinctDistances 12 ≤ 4 := by omega
      refine ⟨hd12_le4, hd13, ?_⟩
      by_cases hplat11 : minimalDistinctDistances 11 = minimalDistinctDistances 12
      · left
        exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
          11 (by omega) hplat11 (by omega)
      · by_cases hplat10 : minimalDistinctDistances 10 = minimalDistinctDistances 11
        · right; left
          exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
            10 (by omega) hplat10 (by omega)
        · right; right
          have hd10_3 : minimalDistinctDistances 10 = 3 := by omega
          have hd9_3 : minimalDistinctDistances 9 = 3 := by omega
          have hd8_3 : minimalDistinctDistances 8 = 3 := by omega
          exact ⟨Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
              8 (by omega) (hd8_3.trans hd9_3.symm) (by omega),
            Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
              9 (by omega) (hd9_3.trans hd10_3.symm) (by omega)⟩

end Erdos91.RoundedHexagonAndCertifiedMultiDeletionFamilies


namespace Erdos91.CayleyMengerSymmetricAndDiameterAdjacentFibers
open scoped Classical
open Finset Minimizer91 PlateauDefinitions91 Erdos91.TwoDistanceCapAndSixNonunique
  Erdos91.ThreeDistanceLevelAndDiameterFiberBounds

/-- **Universal Symmetric-Fiber Cayley–Menger Polynomial Factorization (`∀ d2 r t s2`):**
when `ac = ad = r^2` and `bc = bd = t^2`, the 2D Cayley–Menger polynomial factors as
`cmPoly d2 (r^2) (r^2) (t^2) (t^2) s2 = -s2 * (d2 * s2 - ((r + t)^2 - d2) * (d2 - (r - t)^2))`. -/
theorem cmPoly_symmetric_fiber_factorization (d2 r t s2 : ℝ) :
    cmPoly d2 (r ^ 2) (r ^ 2) (t ^ 2) (t ^ 2) s2 =
      -s2 * (d2 * s2 - ((r + t) ^ 2 - d2) * (d2 - (r - t) ^ 2)) := by
  unfold cmPoly
  ring

/-- **Universal Symmetric Two-Center Fiber Chord Equation (`∀ a b u v r t`):**
if `u ≠ v` both have distance `r` from `a` and distance `t` from `b`, then
`dist a b ^ 2 * dist u v ^ 2 = ((r + t)^2 - dist a b ^ 2) * (dist a b ^ 2 - (r - t)^2)`. -/
theorem symmetric_fiber_chord_sq_eq
    (a b u v : Plane) (r t : ℝ) (huv : u ≠ v)
    (hua : dist u a = r) (hva : dist v a = r)
    (hub : dist u b = t) (hvb : dist v b = t) :
    dist a b ^ 2 * dist u v ^ 2 =
      ((r + t) ^ 2 - dist a b ^ 2) * (dist a b ^ 2 - (r - t) ^ 2) := by
  have hcm := cmPoly_dist_sq_eq_zero a b u v
  rw [dist_comm a u, hua, dist_comm a v, hva, dist_comm b u, hub, dist_comm b v, hvb,
    cmPoly_symmetric_fiber_factorization] at hcm
  have hs_pos : 0 < dist u v ^ 2 := sq_pos_of_pos (dist_pos.mpr huv)
  rcases mul_eq_zero.mp hcm with hs0 | hdiff
  · linarith
  · linarith

/-- **Universal Strict Triangle Inequality on Two-Point Fibers (`∀ a b u v r t`):**
if `a ≠ b` and `u ≠ v` both lie in the `(r, t)`-fiber over `(a, b)`, then
`dist a b ^ 2 < (r + t)^2`, `(r - t)^2 < dist a b ^ 2`, and `dist a b < r + t`. -/
theorem strict_triangle_of_two_point_fiber
    (a b u v : Plane) (r t : ℝ) (hab : a ≠ b) (huv : u ≠ v)
    (hua : dist u a = r) (hva : dist v a = r)
    (hub : dist u b = t) (hvb : dist v b = t) :
    dist a b ^ 2 < (r + t) ^ 2 ∧
      (r - t) ^ 2 < dist a b ^ 2 ∧
      dist a b < r + t := by
  have hchord := symmetric_fiber_chord_sq_eq a b u v r t huv hua hva hub hvb
  have hd_pos : 0 < dist a b := dist_pos.mpr hab
  have hs_pos : 0 < dist u v := dist_pos.mpr huv
  have hd2_pos : 0 < dist a b ^ 2 := sq_pos_of_pos hd_pos
  have hs2_pos : 0 < dist u v ^ 2 := sq_pos_of_pos hs_pos
  have hprod_pos : 0 < ((r + t) ^ 2 - dist a b ^ 2) * (dist a b ^ 2 - (r - t) ^ 2) := by
    rw [← hchord]
    exact mul_pos hd2_pos hs2_pos
  have hr_nn : 0 ≤ r := by rw [← hua]; exact dist_nonneg
  have ht_nn : 0 ≤ t := by rw [← hub]; exact dist_nonneg
  have htri : dist a b ≤ r + t := by
    rw [← hua, ← hub]
    simpa [dist_comm] using dist_triangle a u b
  have hsum_sq : dist a b ^ 2 ≤ (r + t) ^ 2 := by nlinarith
  have hsum_gt : 0 < (r + t) ^ 2 - dist a b ^ 2 := by
    by_contra hle
    have h0 : (r + t) ^ 2 - dist a b ^ 2 = 0 := by linarith
    rw [h0, zero_mul] at hprod_pos
    exact lt_irrefl 0 hprod_pos
  have hdiff_gt : 0 < dist a b ^ 2 - (r - t) ^ 2 :=
    pos_of_mul_pos_right hprod_pos (le_of_lt hsum_gt)
  refine ⟨by linarith, by linarith, ?_⟩
  by_contra hge
  have heq : r + t = dist a b := by linarith
  rw [heq] at hsum_gt
  linarith

/-- **Negative / Collinear Control: Degenerate Fiber Cardinality Cap `≤ 1` (`∀ S a b r t`):**
for any `a ≠ b` and any `r, t : ℝ` with `r + t ≤ dist a b` (collinear or infeasible radii),
`(S.filter (fun v => dist v a = r ∧ dist v b = t)).card ≤ 1`. -/
theorem degenerate_fiber_card_le_one
    (S : Finset Plane) (a b : Plane) (r t : ℝ) (hab : a ≠ b) (hdeg : r + t ≤ dist a b) :
    (S.filter (fun v => dist v a = r ∧ dist v b = t)).card ≤ 1 := by
  by_contra hgt
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (not_le.mp hgt)
  obtain ⟨_, hua, hub⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hva, hvb⟩ := Finset.mem_filter.mp hv
  have hlt := (strict_triangle_of_two_point_fiber a b u v r t hab huv hua hva hub hvb).2.2
  linarith

/-- **Universal Isosceles Fiber Chord Identity and Diameter Window (`∀ S a b u v r`):**
if `u ≠ v` in `S` both have distance `r` to both endpoints of a diameter pair `(a, b)` of `S`,
then `dist u v ^ 2 = 4 * r^2 - dist a b ^ 2` and `dist a b ^ 2 < 4 * r^2 ≤ 2 * dist a b ^ 2`. -/
theorem isosceles_diameter_fiber_chord_sq_and_bounds
    (S : Finset Plane) (a b u v : Plane) (r : ℝ)
    (hab : a ≠ b) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hua : dist u a = r) (hva : dist v a = r)
    (hub : dist u b = r) (hvb : dist v b = r) :
    dist u v ^ 2 = 4 * r ^ 2 - dist a b ^ 2 ∧
      dist a b ^ 2 < 4 * r ^ 2 ∧
      4 * r ^ 2 ≤ 2 * dist a b ^ 2 := by
  have hchord := symmetric_fiber_chord_sq_eq a b u v r r huv hua hva hub hvb
  have hd_pos : 0 < dist a b := dist_pos.mpr hab
  have hs_pos : 0 < dist u v := dist_pos.mpr huv
  have hd2_pos : 0 < dist a b ^ 2 := sq_pos_of_pos hd_pos
  have hs2_pos : 0 < dist u v ^ 2 := sq_pos_of_pos hs_pos
  have hle : dist u v ≤ dist a b := hdiam u hu v hv
  have hsq_le : dist u v ^ 2 ≤ dist a b ^ 2 := by
    nlinarith [dist_nonneg (x := u) (y := v), dist_nonneg (x := a) (y := b)]
  have hrel : dist a b ^ 2 * (dist u v ^ 2 - (4 * r ^ 2 - dist a b ^ 2)) = 0 := by
    linear_combination hchord
  rcases mul_eq_zero.mp hrel with hd0 | h4
  · linarith
  · have heq : dist u v ^ 2 = 4 * r ^ 2 - dist a b ^ 2 := by linarith
    exact ⟨heq, by linarith, by linarith⟩

/-- **Universal Isosceles Diameter-Fiber Cardinality Cap `≤ 1` Outside `(d/2, d/√2]` (`∀ S a b r`):**
for any diameter pair `(a, b)` of `S` and any `r : ℝ` with `4 * r^2 ≤ dist a b ^ 2` or
`2 * dist a b ^ 2 < 4 * r^2` (in particular `r = dist a b`),
`(S.filter (fun v => dist v a = r ∧ dist v b = r)).card ≤ 1`. -/
theorem isosceles_diameter_fiber_card_le_one
    (S : Finset Plane) (a b : Plane) (r : ℝ)
    (hab : a ≠ b) (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hr : 4 * r ^ 2 ≤ dist a b ^ 2 ∨ 2 * dist a b ^ 2 < 4 * r ^ 2) :
    (S.filter (fun v => dist v a = r ∧ dist v b = r)).card ≤ 1 := by
  by_contra hgt
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (not_le.mp hgt)
  obtain ⟨huS, hua, hub⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvS, hva, hvb⟩ := Finset.mem_filter.mp hv
  obtain ⟨_, hlo, hhi⟩ :=
    isosceles_diameter_fiber_chord_sq_and_bounds S a b u v r hab huS hvS huv hdiam hua hva hub hvb
  rcases hr with hle | hgt2 <;> linarith

/-- **Universal Diameter-Adjacent Fiber Chord Equation and $\sqrt{3}$ Magnification (`∀ S a b u v r`):**
if `(a, b)` is a diameter pair of `S` and `u ≠ v` in `S` satisfy `dist u a = dist v a = r`
and `dist u b = dist v b = dist a b`, then:
1. `dist a b ^ 2 * dist u v ^ 2 = r^2 * (4 * dist a b ^ 2 - r^2)`,
2. `3 * r^2 ≤ dist u v ^ 2` and `r < dist u v`,
3. `3 * r^2 < dist a b ^ 2` and `3 * dist a b ^ 4 ≤ (2 * dist a b ^ 2 - r^2)^2`. -/
theorem diameter_adjacent_fiber_chord_sq_and_ratio_cap
    (S : Finset Plane) (a b u v : Plane) (r : ℝ)
    (hab : a ≠ b) (ha : a ∈ S) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hua : dist u a = r) (hva : dist v a = r)
    (hub : dist u b = dist a b) (hvb : dist v b = dist a b) :
    dist a b ^ 2 * dist u v ^ 2 = r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) ∧
      3 * r ^ 2 ≤ dist u v ^ 2 ∧
      r < dist u v ∧
      3 * r ^ 2 < dist a b ^ 2 ∧
      3 * dist a b ^ 4 ≤ (2 * dist a b ^ 2 - r ^ 2) ^ 2 := by
  have hchord := symmetric_fiber_chord_sq_eq a b u v r (dist a b) huv hua hva hub hvb
  have hd_eq : dist a b ^ 2 * dist u v ^ 2 = r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) := by
    linear_combination hchord
  have hd_pos : 0 < dist a b := dist_pos.mpr hab
  have hs_pos : 0 < dist u v := dist_pos.mpr huv
  have hd2_pos : 0 < dist a b ^ 2 := sq_pos_of_pos hd_pos
  have hs2_pos : 0 < dist u v ^ 2 := sq_pos_of_pos hs_pos
  have hr_nn : 0 ≤ r := by rw [← hua]; exact dist_nonneg
  have hr_le_d : r ≤ dist a b := by rw [← hua]; exact hdiam u hu a ha
  have hr2_le_d2 : r ^ 2 ≤ dist a b ^ 2 := by nlinarith
  have hs_le_d : dist u v ≤ dist a b := hdiam u hu v hv
  have hs2_le_d2 : dist u v ^ 2 ≤ dist a b ^ 2 := by
    nlinarith [dist_nonneg (x := u) (y := v)]
  have h3r2_le : 3 * r ^ 2 ≤ dist u v ^ 2 := by
    have h1 : dist a b ^ 2 * (3 * r ^ 2) ≤ r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) := by nlinarith
    rw [← hd_eq] at h1
    exact le_of_mul_le_mul_left h1 hd2_pos
  have hr_pos : 0 < r := by
    by_contra hle0
    have hr0 : r = 0 := by linarith
    rw [hr0] at hd_eq
    nlinarith
  have hr_lt_s : r < dist u v := by
    by_contra hge
    have hs2_le_r2 : dist u v ^ 2 ≤ r ^ 2 := by nlinarith
    nlinarith [sq_pos_of_pos hr_pos]
  have h3r2_lt_d2 : 3 * r ^ 2 < dist a b ^ 2 := by
    by_contra hge
    have h_eq_d2 : r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) - dist a b ^ 4 =
        3 * dist a b ^ 4 - (2 * dist a b ^ 2 - r ^ 2) ^ 2 := by ring
    have h_le : r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) ≤ dist a b ^ 4 := by
      rw [← hd_eq]
      nlinarith
    have h_sub : dist a b ^ 2 ≤ 2 * dist a b ^ 2 - r ^ 2 := by linarith
    have h_up : 2 * dist a b ^ 2 - r ^ 2 ≤ (5 / 3 : ℝ) * dist a b ^ 2 := by linarith
    have h_sq : (2 * dist a b ^ 2 - r ^ 2) ^ 2 ≤ (25 / 9 : ℝ) * dist a b ^ 4 := by nlinarith
    have hd4_pos : 0 < dist a b ^ 4 := by positivity
    linarith
  have h_quartic : 3 * dist a b ^ 4 ≤ (2 * dist a b ^ 2 - r ^ 2) ^ 2 := by
    have h_le : r ^ 2 * (4 * dist a b ^ 2 - r ^ 2) ≤ dist a b ^ 4 := by
      rw [← hd_eq]
      nlinarith
    nlinarith
  exact ⟨hd_eq, h3r2_le, hr_lt_s, h3r2_lt_d2, h_quartic⟩

/-- **Universal Diameter-Adjacent Fiber Cardinality Cap `≤ 1` for `dist a b ^ 2 ≤ 3 * r^2` (`∀ S a b r`):**
for any diameter pair `(a, b)` of `S` and any `r : ℝ` with `dist a b ^ 2 ≤ 3 * r^2`,
both diameter-adjacent fibers `F(r, dist a b)` and `F(dist a b, r)` have cardinality at most `1`. -/
theorem diameter_adjacent_fiber_card_le_one_of_diam_sq_le_three_mul_sq
    (S : Finset Plane) (a b : Plane) (r : ℝ)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist a b)
    (hr : dist a b ^ 2 ≤ 3 * r ^ 2) :
    (S.filter (fun v => dist v a = r ∧ dist v b = dist a b)).card ≤ 1 ∧
      (S.filter (fun v => dist v a = dist a b ∧ dist v b = r)).card ≤ 1 := by
  constructor
  · by_contra hgt
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (not_le.mp hgt)
    obtain ⟨huS, hua, hub⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvS, hva, hvb⟩ := Finset.mem_filter.mp hv
    have hlt := (diameter_adjacent_fiber_chord_sq_and_ratio_cap
      S a b u v r hab ha huS hvS huv hdiam hua hva hub hvb).2.2.2.1
    linarith
  · by_contra hgt
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (not_le.mp hgt)
    obtain ⟨huS, hua, hub⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvS, hva, hvb⟩ := Finset.mem_filter.mp hv
    have hdba : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ dist b a := by
      intro x hx y hy; rw [dist_comm b a]; exact hdiam x hx y hy
    have hlt := (diameter_adjacent_fiber_chord_sq_and_ratio_cap
      S b a u v r hab.symm hb huS hvS huv hdba
      hub hvb (by simpa [dist_comm] using hua) (by simpa [dist_comm] using hva)).2.2.2.1
    rw [dist_comm b a] at hlt
    linarith

end Erdos91.CayleyMengerSymmetricAndDiameterAdjacentFibers


/-! ## Suite 2: Universal Arbitrary-Patch Coordinate Energy and `k`-Deletion Score Theory (`∀ P_coords C_coords D_coords d K`) -/

namespace Erdos91.ArbitraryPatchCoordMultiDeletionTheory
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity
  Erdos91.LatticeMultiDeletionScoreAndPatchFamilies
  Erdos91.TruncatedTriangleAndEquilateralPatchFamilies
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.UnconditionalNaturalDensityOne
open SimilarityEnergy91 (pairEnergy)
open EnergyLevels91 (energy)

/-- Exact integer lattice row energy `∑ q ∈ P_coords, triNormSq (triOffset p q)` on an arbitrary
triangular-lattice coordinate configuration `P_coords : Finset (ℕ × ℕ)`. -/
def triCoordEnergy (P_coords : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : ℕ :=
  P_coords.sum (fun q => triNormSq (triOffset p q))

/-- Exact integer lattice `k`-deletion score `2 * (∑ p ∈ D_coords, triCoordEnergy P_coords p) - hexCoordPairEnergy D_coords`
on an arbitrary coordinate configuration `P_coords : Finset (ℕ × ℕ)`. -/
def triCoordMultiDelScore (P_coords D_coords : Finset (ℕ × ℕ)) : ℕ :=
  2 * (D_coords.sum (triCoordEnergy P_coords)) - hexCoordPairEnergy D_coords

open scoped Classical

/-- **Universal Arbitrary-Patch Coordinate Row-Energy Identity (`∀ P_coords p`):**
for any finite coordinate set `P_coords : Finset (ℕ × ℕ)` and `p : ℕ × ℕ`,
`energy (P_coords.image triPoint) (triPoint p) = (triCoordEnergy P_coords p : ℝ)`. -/
theorem energy_image_triPoint_eq_triCoordEnergy (P_coords : Finset (ℕ × ℕ)) (p : ℕ × ℕ) :
    energy (P_coords.image triPoint) (triPoint p) = ((triCoordEnergy P_coords p : ℕ) : ℝ) := by
  unfold energy triCoordEnergy
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h)]
  push_cast
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact dist_triPoint_sq_eq_triNormSq p q

/-- **Universal Arbitrary-Patch Subset Pair-Energy Domination (`∀ P_coords D_coords`):**
for any `D_coords ⊆ P_coords`, `hexCoordPairEnergy D_coords ≤ D_coords.sum (triCoordEnergy P_coords)`
and `hexCoordPairEnergy D_coords ≤ 2 * D_coords.sum (triCoordEnergy P_coords)`. -/
theorem hexCoordPairEnergy_le_sum_triCoordEnergy
    (P_coords : Finset (ℕ × ℕ)) {D_coords : Finset (ℕ × ℕ)} (hD : D_coords ⊆ P_coords) :
    hexCoordPairEnergy D_coords ≤ D_coords.sum (triCoordEnergy P_coords) ∧
      hexCoordPairEnergy D_coords ≤ 2 * D_coords.sum (triCoordEnergy P_coords) := by
  have hle : hexCoordPairEnergy D_coords ≤ D_coords.sum (triCoordEnergy P_coords) := by
    unfold hexCoordPairEnergy triCoordEnergy
    refine Finset.sum_le_sum (fun p _ => ?_)
    exact Finset.sum_le_sum_of_subset hD
  exact ⟨hle, by omega⟩

/-- **Universal Arbitrary-Patch `k`-Deletion Score Identity (`∀ P_coords D_coords`):**
for any `D_coords ⊆ P_coords`, `D_coords.image triPoint ⊆ P_coords.image triPoint` and
`multiDelScore (P_coords.image triPoint) (D_coords.image triPoint) = (triCoordMultiDelScore P_coords D_coords : ℝ)`. -/
theorem multiDelScore_image_triPoint_eq_triCoordMultiDelScore
    (P_coords : Finset (ℕ × ℕ)) {D_coords : Finset (ℕ × ℕ)} (hD : D_coords ⊆ P_coords) :
    D_coords.image triPoint ⊆ P_coords.image triPoint ∧
      multiDelScore (P_coords.image triPoint) (D_coords.image triPoint) =
        ((triCoordMultiDelScore P_coords D_coords : ℕ) : ℝ) := by
  refine ⟨Finset.image_subset_image hD, ?_⟩
  unfold multiDelScore triCoordMultiDelScore
  rw [Finset.sum_image (fun x _ y _ h => triPoint_injective h),
    pairEnergy_image_triPoint_eq_hexCoordPairEnergy]
  have hsum : (∑ u ∈ D_coords, energy (P_coords.image triPoint) (triPoint u)) =
      ((D_coords.sum (triCoordEnergy P_coords) : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl (fun p _ => energy_image_triPoint_eq_triCoordEnergy P_coords p)
  rw [hsum]
  have hle := (hexCoordPairEnergy_le_sum_triCoordEnergy P_coords hD).2
  push_cast [hle]
  rfl

/-- **Universal Coordinate-to-Planar Diameter Bound (`∀ P_coords a_c b_c`):**
if every pair `p, q ∈ P_coords` satisfies `triNormSq (triOffset p q) ≤ triNormSq (triOffset a_c b_c)`,
then every pair `x, y ∈ P_coords.image triPoint` satisfies
`dist x y ≤ dist (triPoint a_c) (triPoint b_c)`. -/
theorem dist_le_of_mem_image_triPoint_of_triNormSq_le
    (P_coords : Finset (ℕ × ℕ)) (a_c b_c : ℕ × ℕ)
    (hdiam_c : ∀ p ∈ P_coords, ∀ q ∈ P_coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset a_c b_c)) :
    ∀ x ∈ P_coords.image triPoint, ∀ y ∈ P_coords.image triPoint,
      dist x y ≤ dist (triPoint a_c) (triPoint b_c) := by
  intro x hx y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  rw [dist_triPoint_eq p q, dist_triPoint_eq a_c b_c]
  unfold triNorm
  apply Real.sqrt_le_sqrt
  exact_mod_cast hdiam_c p hp q hq

/-- **Universal Coordinate-Core `k`-Deletion Family Theorem on Any Patch `P_coords` (`∀ P_coords C_coords F_coords a_c b_c d K`):**
for any coordinate set `P_coords : Finset (ℕ × ℕ)`, any distance-complete coordinate core
`C_coords ⊆ P_coords`, any diameter pair `a_c, b_c ∈ C_coords` (`0 < triNormSq (triOffset a_c b_c)`),
and any finite family `F_coords` of `d`-element subsets of `P_coords` disjoint from `C_coords`
with `K ≤ (F_coords.image (triCoordMultiDelScore P_coords)).card`, there exist `K` pairwise nonsimilar
`(P_coords.card - d)`-point `d`-deletions of `P_coords.image triPoint` preserving
`distanceSet (P_coords.image triPoint)`. -/
theorem triCoord_multi_deletion_family_of_coord_core
    (P_coords C_coords : Finset (ℕ × ℕ)) (F_coords : Finset (Finset (ℕ × ℕ)))
    (a_c b_c : ℕ × ℕ) (d K : ℕ)
    (hCore : IsDistanceCompleteCore (C_coords.image triPoint) (P_coords.image triPoint))
    (ha_c : a_c ∈ C_coords) (hb_c : b_c ∈ C_coords)
    (hpos_norm : 0 < triNormSq (triOffset a_c b_c))
    (hdiam_c : ∀ p ∈ P_coords, ∀ q ∈ P_coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset a_c b_c))
    (hF : ∀ D_c ∈ F_coords, D_c ⊆ P_coords ∧ Disjoint D_c C_coords ∧ D_c.card = d)
    (hK : K ≤ (F_coords.image (triCoordMultiDelScore P_coords)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = P_coords.card - d ∧
        Erdos91.DistanceErasure.distanceSet A =
          Erdos91.DistanceErasure.distanceSet (P_coords.image triPoint) ∧
        distinctDistances A = distinctDistances (P_coords.image triPoint)) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances (P_coords.image triPoint) ≤
        minimalDistinctDistances (P_coords.card - d) →
      HasAtLeastKNonsimilarMinimizers K (P_coords.card - d)) := by
  let C := C_coords.image triPoint
  let P := P_coords.image triPoint
  let mapSet : Finset (ℕ × ℕ) → Finset Plane := fun D_c => D_c.image triPoint
  let F := F_coords.image mapSet
  have hP_card : P.card = P_coords.card :=
    Finset.card_image_of_injective _ triPoint_injective
  have hab : triPoint a_c ≠ triPoint b_c := by
    intro heq
    have h0 : a_c = b_c := triPoint_injective heq
    subst h0
    have hzero : triNormSq (triOffset a_c a_c) = 0 := by
      unfold triOffset triNormSq
      simp [Nat.dist_self]
    omega
  have haC : triPoint a_c ∈ C := Finset.mem_image_of_mem triPoint ha_c
  have hbC : triPoint b_c ∈ C := Finset.mem_image_of_mem triPoint hb_c
  have hdiam : ∀ x ∈ P, ∀ y ∈ P, dist x y ≤ dist (triPoint a_c) (triPoint b_c) :=
    dist_le_of_mem_image_triPoint_of_triNormSq_le P_coords a_c b_c hdiam_c
  have hF_plane : ∀ D ∈ F, D ⊆ P ∧ Disjoint D C ∧ D.card = d := by
    intro D hD
    obtain ⟨D_c, hD_c, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hsub, hdisj, hcard⟩ := hF D_c hD_c
    refine ⟨Finset.image_subset_image hsub, ?_, ?_⟩
    · refine Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_)
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hx2
      exact Finset.disjoint_left.mp hdisj hp (triPoint_injective heq ▸ hq)
    · rw [Finset.card_image_of_injective _ triPoint_injective, hcard]
  have himg_eq : F.image (multiDelScore P) =
      (F_coords.image (triCoordMultiDelScore P_coords)).image (fun s : ℕ => (s : ℝ)) := by
    ext y
    simp only [F, mapSet, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨D_c, hD_c, rfl⟩, rfl⟩
      have hsub := (hF D_c hD_c).1
      exact ⟨triCoordMultiDelScore P_coords D_c, ⟨D_c, hD_c, rfl⟩,
        (multiDelScore_image_triPoint_eq_triCoordMultiDelScore P_coords hsub).2.symm⟩
    · rintro ⟨s, ⟨D_c, hD_c, rfl⟩, rfl⟩
      have hsub := (hF D_c hD_c).1
      exact ⟨D_c.image triPoint, ⟨D_c, hD_c, rfl⟩,
        (multiDelScore_image_triPoint_eq_triCoordMultiDelScore P_coords hsub).2⟩
  have hK_plane : K ≤ (F.image (multiDelScore P)).card := by
    rw [himg_eq, Finset.card_image_of_injective _ Nat.cast_injective]
    exact hK
  have hres := distance_complete_core_sdiff_family_of_le_card_image_multiDelScore
    C P F (triPoint a_c) (triPoint b_c) d K hCore hab haC hbC hdiam hF_plane hK_plane
  simpa only [hP_card] using hres

/-- **Universal `(P_coords \ C_coords).powersetCard d` Multi-Deletion Family Theorem (`∀ P_coords C_coords a_c b_c d K`):**
direct specialization of `triCoord_multi_deletion_family_of_coord_core` to the full combinatorially
admissible `d`-deletion family `(P_coords \ C_coords).powersetCard d`. -/
theorem triCoord_powersetCard_multi_deletion_family
    (P_coords C_coords : Finset (ℕ × ℕ)) (a_c b_c : ℕ × ℕ) (d K : ℕ)
    (hCore : IsDistanceCompleteCore (C_coords.image triPoint) (P_coords.image triPoint))
    (ha_c : a_c ∈ C_coords) (hb_c : b_c ∈ C_coords)
    (hpos_norm : 0 < triNormSq (triOffset a_c b_c))
    (hdiam_c : ∀ p ∈ P_coords, ∀ q ∈ P_coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset a_c b_c))
    (hK : K ≤ (((P_coords \ C_coords).powersetCard d).image
      (triCoordMultiDelScore P_coords)).card) :
    (∃ G : Finset (Finset Plane),
      G.card = K ∧
      (∀ A ∈ G, A.card = P_coords.card - d ∧
        Erdos91.DistanceErasure.distanceSet A =
          Erdos91.DistanceErasure.distanceSet (P_coords.image triPoint) ∧
        distinctDistances A = distinctDistances (P_coords.image triPoint)) ∧
      (∀ A ∈ G, ∀ B ∈ G, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (distinctDistances (P_coords.image triPoint) ≤
        minimalDistinctDistances (P_coords.card - d) →
      HasAtLeastKNonsimilarMinimizers K (P_coords.card - d)) := by
  have hF : ∀ D_c ∈ (P_coords \ C_coords).powersetCard d,
      D_c ⊆ P_coords ∧ Disjoint D_c C_coords ∧ D_c.card = d :=
    fun _ hD => mem_powersetCard_sdiff_props hD
  exact triCoord_multi_deletion_family_of_coord_core
    P_coords C_coords ((P_coords \ C_coords).powersetCard d)
    a_c b_c d K hCore ha_c hb_c hpos_norm hdiam_c hF hK

end Erdos91.ArbitraryPatchCoordMultiDeletionTheory


/-! ## Suite 3: The 16-Point 7-Distance Half-Corner-Truncated Hexagon `S₁₆` (`d(14) ≤ d(15) ≤ d(16) ≤ 7`), Its Irreducible 5-Point Core, and Negative Controls -/

namespace Erdos91.HalfCornerTruncatedHexagonS16AndCore5
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity
  Erdos91.LatticeMultiDeletionScoreAndPatchFamilies
  Erdos91.ArbitraryPatchCoordMultiDeletionTheory
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet

/-- The 3 alternating corner coordinates `{(0, 2), (2, 0), (0, 4)}` of `hexCoords 5 2 4`,
choosing one endpoint from each of the 3 diameter-64 opposite corner pairs. -/
def halfCorner3 : Finset (ℕ × ℕ) :=
  {(0, 2), (2, 0), (0, 4)}

/-- The 16-point half-corner-truncated hexagon coordinate patch `hexCoords 5 2 4 \ halfCorner3`. -/
def halfCornerHex16Coords : Finset (ℕ × ℕ) :=
  hexCoords 5 2 4 \ halfCorner3

/-- Irreducible 5-point distance-complete coordinate core `{(0, 3), (1, 1), (1, 3), (2, 4), (3, 3)}`
of `halfCornerHex16Coords`. -/
def halfCornerCore5Coords : Finset (ℕ × ℕ) :=
  {(0, 3), (1, 1), (1, 3), (2, 4), (3, 3)}

/-- The 7-element triangular-lattice offset set `(triUtp 4).erase (0, 4)`
with squared norms `{4, 12, 16, 28, 36, 48, 52}`. -/
def halfCornerUtp7 : Finset (ℕ × ℕ) :=
  (triUtp 4).erase (0, 4)

/-- Planar 16-point half-corner-truncated hexagon `halfCornerHex16 = halfCornerHex16Coords.image triPoint`. -/
noncomputable def halfCornerHex16 : Finset Plane :=
  halfCornerHex16Coords.image triPoint

/-- Planar 5-point distance-complete core `halfCornerCore5 = halfCornerCore5Coords.image triPoint`. -/
noncomputable def halfCornerCore5 : Finset Plane :=
  halfCornerCore5Coords.image triPoint

open scoped Classical

/-- **Set-Difference Presentation and Cardinalities of `halfCornerHex16` and `halfCornerCore5` (`∀ p`):**
for every `p ∈ halfCornerCore5Coords`, `triPoint p ∈ halfCornerHex16`,
`halfCornerHex16 = hexSet 5 2 4 \ (halfCorner3.image triPoint)`,
`halfCornerHex16.card = 16`, and `halfCornerCore5.card = 5`. -/
theorem halfCornerHex16_eq_hexSet_sdiff_and_cards
    (p : ℕ × ℕ) (hp : p ∈ halfCornerCore5Coords) :
    triPoint p ∈ halfCornerHex16 ∧
      halfCornerHex16 = hexSet 5 2 4 \ (halfCorner3.image triPoint) ∧
      halfCornerHex16.card = 16 ∧
      halfCornerCore5.card = 5 := by
  have hsub_coords : halfCornerCore5Coords ⊆ halfCornerHex16Coords := by decide
  have hp_mem : triPoint p ∈ halfCornerHex16 :=
    Finset.mem_image_of_mem triPoint (hsub_coords hp)
  have heq_sdiff : halfCornerHex16 = hexSet 5 2 4 \ (halfCorner3.image triPoint) := by
    unfold halfCornerHex16 halfCornerHex16Coords hexSet
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
      refine ⟨⟨q, hq1, rfl⟩, ?_⟩
      rintro ⟨r, hr, heq⟩
      exact hq2 (triPoint_injective heq ▸ hr)
    · rintro ⟨⟨q, hq1, rfl⟩, hnot⟩
      exact ⟨q, ⟨hq1, fun hq2 => hnot ⟨q, hq2, rfl⟩⟩, rfl⟩
  have hcard16 : halfCornerHex16.card = 16 := by
    unfold halfCornerHex16
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  have hcard5 : halfCornerCore5.card = 5 := by
    unfold halfCornerCore5
    rw [Finset.card_image_of_injective _ triPoint_injective]
    rfl
  exact ⟨hp_mem, heq_sdiff, hcard16, hcard5⟩

/-- **Exact 16-Point 7-Distance Half-Corner-Truncated Hexagon & 5-Point Core Theorem (`∀ p`):**
every `p ∈ halfCornerCore5Coords` maps into `halfCornerHex16`, `halfCornerHex16.card = 16`,
`halfCornerCore5.card = 5`, `IsDistanceCompleteCore halfCornerCore5 halfCornerHex16`,
`distanceSet halfCornerHex16 = halfCornerUtp7.image triNorm`, `distinctDistances halfCornerHex16 = 7`,
and consequently `minimalDistinctDistances 16 ≤ 7`, `minimalDistinctDistances 15 ≤ 7`,
and `minimalDistinctDistances 14 ≤ 7`. -/
theorem card_and_distanceSet_halfCornerHex16_and_core5
    (p : ℕ × ℕ) (hp : p ∈ halfCornerCore5Coords) :
    triPoint p ∈ halfCornerHex16 ∧
      halfCornerHex16.card = 16 ∧
      halfCornerCore5.card = 5 ∧
      IsDistanceCompleteCore halfCornerCore5 halfCornerHex16 ∧
      Erdos91.DistanceErasure.distanceSet halfCornerHex16 = halfCornerUtp7.image triNorm ∧
      distinctDistances halfCornerHex16 = 7 ∧
      minimalDistinctDistances 16 ≤ 7 ∧
      minimalDistinctDistances 15 ≤ 7 ∧
      minimalDistinctDistances 14 ≤ 7 := by
  obtain ⟨hp_mem, _, hcard16, hcard5⟩ := halfCornerHex16_eq_hexSet_sdiff_and_cards p hp
  have hsub_coords : halfCornerCore5Coords ⊆ halfCornerHex16Coords := by decide
  have hsub_core : halfCornerCore5 ⊆ halfCornerHex16 := Finset.image_subset_image hsub_coords
  have h_off : ∀ a ∈ halfCornerHex16Coords, ∀ b ∈ halfCornerHex16Coords, a ≠ b →
      triOffset a b ∈ halfCornerUtp7 := by decide
  have hupper : Erdos91.DistanceErasure.distanceSet halfCornerHex16 ⊆ halfCornerUtp7.image triNorm := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (Erdos91.DistanceErasure.mem_distanceSet _ _).mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg triPoint h)
    rw [dist_triPoint_eq a b]
    exact Finset.mem_image_of_mem triNorm (h_off a ha b hb hab)
  have h_edge : ∀ a b : ℕ × ℕ, a ∈ halfCornerCore5Coords → b ∈ halfCornerCore5Coords → a ≠ b →
      triNorm (triOffset a b) ∈ Erdos91.DistanceErasure.distanceSet halfCornerCore5 := by
    intro a b ha hb hab
    exact (Erdos91.DistanceErasure.mem_distanceSet _ _).mpr
      ⟨triPoint a, Finset.mem_image_of_mem triPoint ha,
       triPoint b, Finset.mem_image_of_mem triPoint hb,
       fun h => hab (triPoint_injective h), dist_triPoint_eq a b⟩
  have hlower : halfCornerUtp7.image triNorm ⊆ Erdos91.DistanceErasure.distanceSet halfCornerCore5 := by
    intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu_all : ∀ v ∈ halfCornerUtp7,
        v = (0, 1) ∨ v = (0, 2) ∨ v = (0, 3) ∨ v = (1, 1) ∨
        v = (1, 2) ∨ v = (1, 3) ∨ v = (2, 2) := by decide
    rcases hu_all u hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_edge (0, 3) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (1, 1) (1, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (3, 3) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (1, 1) (by decide) (by decide) (by decide)
    · exact h_edge (0, 3) (2, 4) (by decide) (by decide) (by decide)
    · exact h_edge (1, 1) (2, 4) (by decide) (by decide) (by decide)
    · exact h_edge (1, 1) (3, 3) (by decide) (by decide) (by decide)
  have hDS_core : Erdos91.DistanceErasure.distanceSet halfCornerCore5 = halfCornerUtp7.image triNorm :=
    Finset.Subset.antisymm ((distanceSet_mono hsub_core).trans hupper) hlower
  have hDS_s16 : Erdos91.DistanceErasure.distanceSet halfCornerHex16 = halfCornerUtp7.image triNorm :=
    Finset.Subset.antisymm hupper (hlower.trans (distanceSet_mono hsub_core))
  have hCore : IsDistanceCompleteCore halfCornerCore5 halfCornerHex16 :=
    ⟨hsub_core, hDS_core.trans hDS_s16.symm⟩
  have hdd : distinctDistances halfCornerHex16 = 7 := by
    change (Erdos91.DistanceErasure.distanceSet halfCornerHex16).card = 7
    rw [hDS_s16, card_image_triNorm_eq_card_image_triNormSq]
    rfl
  have hd16 : minimalDistinctDistances 16 ≤ 7 :=
    (minimal_le halfCornerHex16 16 hcard16).trans hdd.le
  have hd15 : minimalDistinctDistances 15 ≤ 7 :=
    (MinimumMonotone91.minimum_monotone (by omega : 15 ≤ 16)).trans hd16
  have hd14 : minimalDistinctDistances 14 ≤ 7 :=
    (MinimumMonotone91.minimum_monotone (by omega : 14 ≤ 15)).trans hd15
  exact ⟨hp_mem, hcard16, hcard5, hCore, hDS_s16, hdd, hd16, hd15, hd14⟩

/-- **Universal `k`-Deletion Distance-Set Invariance and Conditional Optimality on `halfCornerHex16` (`∀ D d`):**
for every `D ⊆ halfCornerHex16` disjoint from `halfCornerCore5` with `D.card = d`,
`halfCornerHex16 \ D` has `16 - d` points and exact 7-element distance set `distanceSet halfCornerHex16`
(`minimalDistinctDistances (16 - d) ≤ 7`), and is globally optimal whenever `7 ≤ d(16 - d)`. -/
theorem halfCornerHex16_sdiff_distanceSet_and_optimal_of_seven_le
    (D : Finset Plane) (d : ℕ) (hDP : D ⊆ halfCornerHex16)
    (hDC : Disjoint D halfCornerCore5) (hDcard : D.card = d) :
    (halfCornerHex16 \ D).card = 16 - d ∧
      Erdos91.DistanceErasure.distanceSet (halfCornerHex16 \ D) =
        Erdos91.DistanceErasure.distanceSet halfCornerHex16 ∧
      distinctDistances (halfCornerHex16 \ D) = 7 ∧
      minimalDistinctDistances (16 - d) ≤ 7 ∧
      (7 ≤ minimalDistinctDistances (16 - d) → IsOptimal (halfCornerHex16 \ D) (16 - d)) := by
  obtain ⟨_, hcard16, _, hCore, _, hdd7, _, _, _⟩ :=
    card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)
  obtain ⟨hDS, hdd⟩ := distanceSet_sdiff_eq_of_isDistanceCompleteCore
    halfCornerCore5 halfCornerHex16 D hCore hDC
  have hcard : (halfCornerHex16 \ D).card = 16 - d := by
    rw [Finset.card_sdiff_of_subset hDP, hcard16, hDcard]
  have hdd_eq : distinctDistances (halfCornerHex16 \ D) = 7 := hdd.trans hdd7
  have hmin_le : minimalDistinctDistances (16 - d) ≤ 7 :=
    (minimal_le (halfCornerHex16 \ D) (16 - d) hcard).trans hdd_eq.le
  refine ⟨hcard, hDS, hdd_eq, hmin_le, ?_⟩
  intro h7
  exact ⟨hcard, by omega⟩

/-- **Shared Diameter Pair `(triPoint (1, 1), triPoint (2, 4))` of `halfCornerHex16` Inside `halfCornerCore5` (`∀ x y`):**
the core vertices `triPoint (1, 1)` and `triPoint (2, 4)` in `halfCornerCore5` have squared distance `52`
and bound every pairwise distance `dist x y` in `halfCornerHex16`. -/
theorem halfCornerHex16_diameter_pair_in_core5
    (x y : Plane) (hx : x ∈ halfCornerHex16) (hy : y ∈ halfCornerHex16) :
    triPoint (1, 1) ∈ halfCornerCore5 ∧
      triPoint (2, 4) ∈ halfCornerCore5 ∧
      triPoint (1, 1) ≠ triPoint (2, 4) ∧
      dist (triPoint (1, 1)) (triPoint (2, 4)) ^ 2 = 52 ∧
      dist x y ≤ dist (triPoint (1, 1)) (triPoint (2, 4)) := by
  have ha : triPoint (1, 1) ∈ halfCornerCore5 :=
    Finset.mem_image_of_mem triPoint (by decide : (1, 1) ∈ halfCornerCore5Coords)
  have hb : triPoint (2, 4) ∈ halfCornerCore5 :=
    Finset.mem_image_of_mem triPoint (by decide : (2, 4) ∈ halfCornerCore5Coords)
  have hab : triPoint (1, 1) ≠ triPoint (2, 4) :=
    fun h => (by decide : (1, 1) ≠ (2, 4)) (triPoint_injective h)
  have hsq : dist (triPoint (1, 1)) (triPoint (2, 4)) ^ 2 = 52 := by
    rw [dist_triPoint_sq_eq_triNormSq]
    norm_num [triOffset, triNormSq, Nat.dist]
  have hdiam_c : ∀ p ∈ halfCornerHex16Coords, ∀ q ∈ halfCornerHex16Coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (1, 1) (2, 4)) := by decide
  have hle := dist_le_of_mem_image_triPoint_of_triNormSq_le
    halfCornerHex16Coords (1, 1) (2, 4) hdiam_c x hx y hy
  exact ⟨ha, hb, hab, hsq, hle⟩

/-- **Negative Control 1: Core-Violating Deletion Erases Diameter `52` (`∀ p q`):**
deleting the 4 vertices `{(0, 3), (1, 1), (2, 4), (4, 0)}` (which intersect `halfCornerCore5Coords`)
from `halfCornerHex16Coords` strictly reduces all surviving squared distances to `≤ 48`, erasing
the diameter `√52` from `distanceSet`. -/
theorem halfCornerCore5_violation_erases_diameter_52
    (p q : ℕ × ℕ)
    (hp : p ∈ halfCornerHex16Coords \ {(0, 3), (1, 1), (2, 4), (4, 0)})
    (hq : q ∈ halfCornerHex16Coords \ {(0, 3), (1, 1), (2, 4), (4, 0)}) :
    triNormSq (triOffset p q) ≤ 48 ∧ dist (triPoint p) (triPoint q) ^ 2 ≤ 48 := by
  have h_le : ∀ a ∈ halfCornerHex16Coords \ {(0, 3), (1, 1), (2, 4), (4, 0)},
      ∀ b ∈ halfCornerHex16Coords \ {(0, 3), (1, 1), (2, 4), (4, 0)},
        triNormSq (triOffset a b) ≤ 48 := by decide
  have h1 := h_le p hp q hq
  refine ⟨h1, ?_⟩
  rw [dist_triPoint_sq_eq_triNormSq]
  exact_mod_cast h1

/-- **Negative Control 2: Irreducibility / Minimality of the 5-Point Core `halfCornerCore5Coords` (`∀ u`):**
every single-point deletion `halfCornerCore5Coords.erase u` (`u ∈ halfCornerCore5Coords`) realizes
at most `6 < 7` distinct positive distances, so no 4-point subset of `halfCornerCore5` is distance-complete
for `halfCornerHex16`. -/
theorem halfCornerCore5_irreducible_control
    (u : ℕ × ℕ) (hu : u ∈ halfCornerCore5Coords) :
    (((halfCornerCore5Coords.erase u).offDiag.image
      (fun pq => triNormSq (triOffset pq.1 pq.2))).card ≤ 6) ∧
      ¬ IsDistanceCompleteCore ((halfCornerCore5Coords.erase u).image triPoint) halfCornerHex16 := by
  have h_le6 : ∀ v ∈ halfCornerCore5Coords,
      ((halfCornerCore5Coords.erase v).offDiag.image
        (fun pq => triNormSq (triOffset pq.1 pq.2))).card ≤ 6 := by decide
  have hle := h_le6 u hu
  refine ⟨hle, ?_⟩
  intro hCore
  obtain ⟨_, hdd_eq⟩ := distanceSet_eq_of_subset_between
    ((halfCornerCore5Coords.erase u).image triPoint)
    ((halfCornerCore5Coords.erase u).image triPoint)
    halfCornerHex16 hCore Subset.rfl hCore.1
  have hdd7 : distinctDistances halfCornerHex16 = 7 :=
    (card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)).2.2.2.2.2.1
  have hsub : Erdos91.DistanceErasure.distanceSet ((halfCornerCore5Coords.erase u).image triPoint) ⊆
      (((halfCornerCore5Coords.erase u).offDiag.image
        (fun pq => triNormSq (triOffset pq.1 pq.2))).image (fun n : ℕ => Real.sqrt (n : ℝ))) := by
    intro r hr
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (Erdos91.DistanceErasure.mem_distanceSet _ _).mp hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg triPoint h)
    rw [dist_triPoint_eq a b]
    unfold triNorm
    apply Finset.mem_image_of_mem
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
  have hcard_le : distinctDistances ((halfCornerCore5Coords.erase u).image triPoint) ≤ 6 := by
    change (Erdos91.DistanceErasure.distanceSet ((halfCornerCore5Coords.erase u).image triPoint)).card ≤ 6
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hle)
  omega

end Erdos91.HalfCornerTruncatedHexagonS16AndCore5


/-! ## Suite 4: Certified Multi-Deletion Families for `n = 10..15` on `S₁₆`, `R₁₃`, and `H₂`, and Unconditional `n = 10..15` Nonuniqueness Dichotomies -/

namespace Erdos91.CertifiedMultiDeletionFamilies10To15AndStepSevenDichotomy
open Finset Minimizer91 PlateauDefinitions91
  Erdos91.DistanceCompleteCoreDeletionInvariance
  Erdos91.MultiDeletionScoreInvarianceAndCoreMultiplicity
  Erdos91.LatticeMultiDeletionScoreAndPatchFamilies
  Erdos91.RoundedHexagonAndCertifiedMultiDeletionFamilies
  Erdos91.ArbitraryPatchCoordMultiDeletionTheory
  Erdos91.HalfCornerTruncatedHexagonS16AndCore5
  Erdos91.TriangularLatticeHexagonAndSub130Majority
  Erdos91.SymbolicHexagonExactCardinalityAndDistanceSet
  Erdos91.UnconditionalNaturalDensityOne
  Erdos91.TwoDistanceCapAndSixNonunique

open scoped Classical

/-- **Certified 8-Configuration Single-Deletion (`n = 15`) and 31-Configuration Pair-Deletion (`n = 14`) Families on `halfCornerHex16` (`∀ K₁ ≤ 8, ∀ K₂ ≤ 31`):**
for every `K₁ ≤ 8` and `K₂ ≤ 31`, `halfCornerHex16` admits `K₁` pairwise nonsimilar `15`-point
1-deletions and `K₂` pairwise nonsimilar `14`-point 2-deletions outside `halfCornerCore5`,
all preserving the 7-element distance set `halfCornerUtp7.image triNorm` (`distinctDistances A = 7`),
and certifying `(7 ≤ d(15) → HasAtLeastKNonsimilarMinimizers K₁ 15)` and
`(7 ≤ d(14) → HasAtLeastKNonsimilarMinimizers K₂ 14)`. -/
theorem halfCornerHex16_fifteen_and_fourteen_point_multi_deletion_families
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 8) (hK₂ : K₂ ≤ 31) :
    ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 15 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances 15 → HasAtLeastKNonsimilarMinimizers K₁ 15)) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 14 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances 14 → HasAtLeastKNonsimilarMinimizers K₂ 14)) := by
  obtain ⟨_, _, _, hCore, hDS7, hdd7, _, _, _⟩ :=
    card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)
  have hcard16_c : halfCornerHex16Coords.card = 16 := rfl
  have hdiam_c : ∀ p ∈ halfCornerHex16Coords, ∀ q ∈ halfCornerHex16Coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (1, 1) (2, 4)) := by decide
  have hres1 := triCoord_powersetCard_multi_deletion_family
    halfCornerHex16Coords halfCornerCore5Coords (1, 1) (2, 4) 1 K₁
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁.trans_eq rfl)
  have hres2 := triCoord_powersetCard_multi_deletion_family
    halfCornerHex16Coords halfCornerCore5Coords (1, 1) (2, 4) 2 K₂
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₂.trans_eq rfl)
  change ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 16 - 1 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances (16 - 1) → HasAtLeastKNonsimilarMinimizers K₁ (16 - 1))) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 16 - 2 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances (16 - 2) → HasAtLeastKNonsimilarMinimizers K₂ (16 - 2)))
  change IsDistanceCompleteCore (halfCornerCore5Coords.image triPoint)
    (halfCornerHex16Coords.image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet (halfCornerHex16Coords.image triPoint) =
    halfCornerUtp7.image triNorm at hDS7
  change distinctDistances (halfCornerHex16Coords.image triPoint) = 7 at hdd7
  exact ⟨by simpa only [hcard16_c, hDS7, hdd7] using hres1,
    by simpa only [hcard16_c, hDS7, hdd7] using hres2⟩

/-- **Certified 73-Configuration 3-Deletion (`n = 13`) and 62-Configuration 4-Deletion (`n = 12`) Families on `halfCornerHex16` (`∀ K₁ ≤ 73, ∀ K₂ ≤ 62`):**
for every `K₁ ≤ 73` and `K₂ ≤ 62`, `halfCornerHex16` admits `K₁` pairwise nonsimilar `13`-point
3-deletions and `K₂` pairwise nonsimilar `12`-point 4-deletions outside `halfCornerCore5`,
all preserving the 7-element distance set `halfCornerUtp7.image triNorm` (`distinctDistances A = 7`),
and certifying `(7 ≤ d(13) → HasAtLeastKNonsimilarMinimizers K₁ 13)` and
`(7 ≤ d(12) → HasAtLeastKNonsimilarMinimizers K₂ 12)`. -/
theorem halfCornerHex16_thirteen_and_twelve_point_multi_deletion_families
    (K₁ K₂ : ℕ) (hK₁ : K₁ ≤ 73) (hK₂ : K₂ ≤ 62) :
    ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 13 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances 13 → HasAtLeastKNonsimilarMinimizers K₁ 13)) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 12 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances 12 → HasAtLeastKNonsimilarMinimizers K₂ 12)) := by
  obtain ⟨_, _, _, hCore, hDS7, hdd7, _, _, _⟩ :=
    card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)
  have hcard16_c : halfCornerHex16Coords.card = 16 := rfl
  have hdiam_c : ∀ p ∈ halfCornerHex16Coords, ∀ q ∈ halfCornerHex16Coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (1, 1) (2, 4)) := by decide
  have hres3 := triCoord_powersetCard_multi_deletion_family
    halfCornerHex16Coords halfCornerCore5Coords (1, 1) (2, 4) 3 K₁
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁.trans_eq rfl)
  have hres4 := triCoord_powersetCard_multi_deletion_family
    halfCornerHex16Coords halfCornerCore5Coords (1, 1) (2, 4) 4 K₂
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₂.trans_eq rfl)
  change ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 16 - 3 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances (16 - 3) → HasAtLeastKNonsimilarMinimizers K₁ (16 - 3))) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 16 - 4 ∧
        Erdos91.DistanceErasure.distanceSet A = halfCornerUtp7.image triNorm ∧
        distinctDistances A = 7) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (7 ≤ minimalDistinctDistances (16 - 4) → HasAtLeastKNonsimilarMinimizers K₂ (16 - 4)))
  change IsDistanceCompleteCore (halfCornerCore5Coords.image triPoint)
    (halfCornerHex16Coords.image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet (halfCornerHex16Coords.image triPoint) =
    halfCornerUtp7.image triNorm at hDS7
  change distinctDistances (halfCornerHex16Coords.image triPoint) = 7 at hdd7
  exact ⟨by simpa only [hcard16_c, hDS7, hdd7] using hres3,
    by simpa only [hcard16_c, hDS7, hdd7] using hres4⟩

/-- **Certified 3-Configuration (`n = 12`), 11-Configuration (`n = 11`), and 25-Configuration (`n = 10`) 6-Distance Families on `roundedHex13` (`∀ K₁ ≤ 3, ∀ K₂ ≤ 11, ∀ K₃ ≤ 25`):**
for every `K₁ ≤ 3`, `K₂ ≤ 11`, and `K₃ ≤ 25`, the 13-point rounded hexagon `roundedHex13` admits
`K₁` (`n = 12`, `d = 1`), `K₂` (`n = 11`, `d = 2`), and `K₃` (`n = 10`, `d = 3`) pairwise nonsimilar
6-distance deletions outside `roundedHexCore4`, all preserving `roundedHexUtp6.image triNorm`
(`distinctDistances A = 6`). -/
theorem roundedHex13_twelve_eleven_ten_point_multi_deletion_families
    (K₁ K₂ K₃ : ℕ) (hK₁ : K₁ ≤ 3) (hK₂ : K₂ ≤ 11) (hK₃ : K₃ ≤ 25) :
    ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 12 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances 12 → HasAtLeastKNonsimilarMinimizers K₁ 12)) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 11 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances 11 → HasAtLeastKNonsimilarMinimizers K₂ 11)) ∧
    ((∃ G₃ : Finset (Finset Plane),
      G₃.card = K₃ ∧
      (∀ A ∈ G₃, A.card = 10 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₃, ∀ B ∈ G₃, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances 10 → HasAtLeastKNonsimilarMinimizers K₃ 10)) := by
  obtain ⟨_, _, _, hCore, hDS6, hdd6, _⟩ :=
    card_and_distanceSet_roundedHex13_and_core4 (0, 3) (by decide)
  have hcard13_c : roundedHex13Coords.card = 13 := rfl
  have hdiam_c : ∀ p ∈ roundedHex13Coords, ∀ q ∈ roundedHex13Coords,
      triNormSq (triOffset p q) ≤ triNormSq (triOffset (0, 3) (4, 1)) := by decide
  have hres1 := triCoord_powersetCard_multi_deletion_family
    roundedHex13Coords roundedHexCore4Coords (0, 3) (4, 1) 1 K₁
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₁.trans_eq rfl)
  have hres2 := triCoord_powersetCard_multi_deletion_family
    roundedHex13Coords roundedHexCore4Coords (0, 3) (4, 1) 2 K₂
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₂.trans_eq rfl)
  have hres3 := triCoord_powersetCard_multi_deletion_family
    roundedHex13Coords roundedHexCore4Coords (0, 3) (4, 1) 3 K₃
    hCore (by decide) (by decide) (by decide) hdiam_c (hK₃.trans_eq rfl)
  change ((∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 13 - 1 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances (13 - 1) → HasAtLeastKNonsimilarMinimizers K₁ (13 - 1))) ∧
    ((∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 13 - 2 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances (13 - 2) → HasAtLeastKNonsimilarMinimizers K₂ (13 - 2))) ∧
    ((∃ G₃ : Finset (Finset Plane),
      G₃.card = K₃ ∧
      (∀ A ∈ G₃, A.card = 13 - 3 ∧
        Erdos91.DistanceErasure.distanceSet A = roundedHexUtp6.image triNorm ∧
        distinctDistances A = 6) ∧
      (∀ A ∈ G₃, ∀ B ∈ G₃, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
      (6 ≤ minimalDistinctDistances (13 - 3) → HasAtLeastKNonsimilarMinimizers K₃ (13 - 3)))
  change IsDistanceCompleteCore (roundedHexCore4Coords.image triPoint)
    (roundedHex13Coords.image triPoint) at hCore
  change Erdos91.DistanceErasure.distanceSet (roundedHex13Coords.image triPoint) =
    roundedHexUtp6.image triNorm at hDS6
  change distinctDistances (roundedHex13Coords.image triPoint) = 6 at hdd6
  exact ⟨by simpa only [hcard13_c, hDS6, hdd6] using hres1,
    by simpa only [hcard13_c, hDS6, hdd6] using hres2,
    by simpa only [hcard13_c, hDS6, hdd6] using hres3⟩

/-- **Certified 40-Configuration 4-Deletion (`n = 15`), 46-Configuration 5-Deletion (`n = 14`), and 37-Configuration 6-Deletion (`n = 13`) Families on `H_2 = hexSet 5 2 4` (`∀ K₁ ≤ 40, ∀ K₂ ≤ 46, ∀ K₃ ≤ 37`):**
for every `K₁ ≤ 40`, `K₂ ≤ 46`, and `K₃ ≤ 37`, the 19-point regular hexagon `hexSet 5 2 4` admits
`K₁` (`n = 15`), `K₂` (`n = 14`), and `K₃` (`n = 13`) pairwise nonsimilar deletions outside
`hexRightCore 2`, all preserving the 8-element distance set `(triUtp 4).image triNorm`. -/
theorem hexSet_5_2_4_fifteen_fourteen_thirteen_point_multi_deletion_families
    (K₁ K₂ K₃ : ℕ) (hK₁ : K₁ ≤ 40) (hK₂ : K₂ ≤ 46) (hK₃ : K₃ ≤ 37) :
    (∃ G₁ : Finset (Finset Plane),
      G₁.card = K₁ ∧
      (∀ A ∈ G₁, A.card = 15 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₁, ∀ B ∈ G₁, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₂ : Finset (Finset Plane),
      G₂.card = K₂ ∧
      (∀ A ∈ G₂, A.card = 14 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₂, ∀ B ∈ G₂, A ≠ B → ¬ DilationEquivSimilar A B)) ∧
    (∃ G₃ : Finset (Finset Plane),
      G₃.card = K₃ ∧
      (∀ A ∈ G₃, A.card = 13 ∧
        Erdos91.DistanceErasure.distanceSet A = (triUtp 4).image triNorm ∧
        distinctDistances A = 8) ∧
      (∀ A ∈ G₃, ∀ B ∈ G₃, A ≠ B → ¬ DilationEquivSimilar A B)) := by
  have hcard19 : (hexSet 5 2 4).card = 19 := Erdos91.ExactHexagonDistanceCountsR1To18.card_hexSet_regular_2
  have hdd8 : ((triUtp 4).image triNormSq).card = 8 := rfl
  have hres4 := (hexSet_regular_multi_deletion_family_of_le_card_image 2 4 K₁ (by omega) (hK₁.trans_eq rfl)).1
  have hres5 := (hexSet_regular_multi_deletion_family_of_le_card_image 2 5 K₂ (by omega) (hK₂.trans_eq rfl)).1
  have hres6 := (hexSet_regular_multi_deletion_family_of_le_card_image 2 6 K₃ (by omega) (hK₃.trans_eq rfl)).1
  exact ⟨by simpa only [hcard19, hdd8] using hres4,
    by simpa only [hcard19, hdd8] using hres5,
    by simpa only [hcard19, hdd8] using hres6⟩

/-- **Conditional `n = 14, 15` Nonuniqueness & `K`-Multiplicity Dichotomy Under `6 ≤ d(13)` (`∀ K₁₄ ≤ 31, ∀ K₁₅ ≤ 8`):**
if `6 ≤ minimalDistinctDistances 13` (so `d(13) = 6`), then across `n = 14, 15, 16`:
1. either `d(14) = 7 ∧ d(15) = 7 ∧ d(16) = 7 ∧ HasAtLeastKNonsimilarMinimizers K₁₄ 14 ∧ HasAtLeastKNonsimilarMinimizers K₁₅ 15`,
2. or `d(14) = 6 ∧ d(15) = 7 ∧ d(16) = 7 ∧ HasAtLeastKNonsimilarMinimizers K₁₅ 15`,
3. or `d(14) = 6 ∧ d(15) = 6 ∧ ¬ UniqueMinimizer 14`. -/
theorem fourteen_fifteen_nonunique_or_multiplicity_of_six_le_thirteen
    (K₁₄ K₁₅ : ℕ) (hK₁₄ : K₁₄ ≤ 31) (hK₁₅ : K₁₅ ≤ 8)
    (h6 : 6 ≤ minimalDistinctDistances 13) :
    (minimalDistinctDistances 14 = 7 ∧ minimalDistinctDistances 15 = 7 ∧
      minimalDistinctDistances 16 = 7 ∧
      HasAtLeastKNonsimilarMinimizers K₁₄ 14 ∧ HasAtLeastKNonsimilarMinimizers K₁₅ 15) ∨
    (minimalDistinctDistances 14 = 6 ∧ minimalDistinctDistances 15 = 7 ∧
      minimalDistinctDistances 16 = 7 ∧
      HasAtLeastKNonsimilarMinimizers K₁₅ 15) ∨
    (minimalDistinctDistances 14 = 6 ∧ minimalDistinctDistances 15 = 6 ∧
      ¬ UniqueMinimizer 14) := by
  obtain ⟨⟨_, hfam15⟩, ⟨_, hfam14⟩⟩ :=
    halfCornerHex16_fifteen_and_fourteen_point_multi_deletion_families K₁₅ K₁₄ hK₁₅ hK₁₄
  obtain ⟨_, _, _, _, _, _, hd16, hd15, hd14⟩ :=
    card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)
  have hm1314 := MinimumMonotone91.minimum_monotone (by omega : 13 ≤ 14)
  have hm1415 := MinimumMonotone91.minimum_monotone (by omega : 14 ≤ 15)
  have hm1516 := MinimumMonotone91.minimum_monotone (by omega : 15 ≤ 16)
  by_cases hd15_7 : 7 ≤ minimalDistinctDistances 15
  · by_cases hd14_7 : 7 ≤ minimalDistinctDistances 14
    · left
      exact ⟨by omega, by omega, by omega, hfam14 hd14_7, hfam15 hd15_7⟩
    · right; left
      exact ⟨by omega, by omega, by omega, hfam15 hd15_7⟩
  · right; right
    have hd14_eq : minimalDistinctDistances 14 = 6 := by omega
    have hd15_eq : minimalDistinctDistances 15 = 6 := by omega
    refine ⟨hd14_eq, hd15_eq, ?_⟩
    exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
      14 (by omega) (hd14_eq.trans hd15_eq.symm) (by omega)

/-- **Unconditional `n ∈ {10, 11, 12, 14, 15}` Nonuniqueness & `K`-Multiplicity Synthesis (`∀ K₁₄ ≤ 31, ∀ K₁₅ ≤ 8`):**
combining `d(7) = 3`, `d(12) ≤ 5` (`hexSet 4 1 3`), `d(13) ≤ 6` (`roundedHex13`), and
`d(14) ≤ d(15) ≤ d(16) ≤ 7` (`halfCornerHex16`), at least one of the following holds unconditionally:
1. `d(15) = 7 ∧ d(16) = 7 ∧ HasAtLeastKNonsimilarMinimizers K₁₅ 15` (and if `d(14) = 7`, also `HasAtLeastKNonsimilarMinimizers K₁₄ 14`),
2. `d(14) = 6 ∧ d(15) = 6 ∧ ¬ UniqueMinimizer 14`,
3. `d(12) = 5 ∧ d(13) = 5 ∧ ¬ UniqueMinimizer 12`,
4. `d(12) ≤ 4 ∧ (¬ UniqueMinimizer 11 ∨ ¬ UniqueMinimizer 10)`. -/
theorem unconditional_ten_eleven_twelve_fourteen_fifteen_nonuniqueness
    (K₁₄ K₁₅ : ℕ) (hK₁₄ : K₁₄ ≤ 31) (hK₁₅ : K₁₅ ≤ 8) :
    (minimalDistinctDistances 15 = 7 ∧ minimalDistinctDistances 16 = 7 ∧
      HasAtLeastKNonsimilarMinimizers K₁₅ 15 ∧
      (7 ≤ minimalDistinctDistances 14 → HasAtLeastKNonsimilarMinimizers K₁₄ 14)) ∨
    (minimalDistinctDistances 14 = 6 ∧ minimalDistinctDistances 15 = 6 ∧
      ¬ UniqueMinimizer 14) ∨
    (minimalDistinctDistances 12 = 5 ∧ minimalDistinctDistances 13 = 5 ∧
      ¬ UniqueMinimizer 12) ∨
    (minimalDistinctDistances 12 ≤ 4 ∧
      (¬ UniqueMinimizer 11 ∨ ¬ UniqueMinimizer 10)) := by
  obtain ⟨⟨_, hfam15⟩, ⟨_, hfam14⟩⟩ :=
    halfCornerHex16_fifteen_and_fourteen_point_multi_deletion_families K₁₅ K₁₄ hK₁₅ hK₁₄
  obtain ⟨_, _, _, _, _, _, hd16, hd15, hd14⟩ :=
    card_and_distanceSet_halfCornerHex16_and_core5 (0, 3) (by decide)
  have hd7 : minimalDistinctDistances 7 = 3 := minimalDistinctDistances_seven
  have hd12 : minimalDistinctDistances 12 ≤ 5 := minimalDistinctDistances_12_le_5
  have hd13 : minimalDistinctDistances 13 ≤ 6 :=
    (card_and_distanceSet_roundedHex13_and_core4 (0, 3) (by decide)).2.2.2.2.2.2
  have hm710 := MinimumMonotone91.minimum_monotone (by omega : 7 ≤ 10)
  have hm1011 := MinimumMonotone91.minimum_monotone (by omega : 10 ≤ 11)
  have hm1112 := MinimumMonotone91.minimum_monotone (by omega : 11 ≤ 12)
  have hm1213 := MinimumMonotone91.minimum_monotone (by omega : 12 ≤ 13)
  have hm1314 := MinimumMonotone91.minimum_monotone (by omega : 13 ≤ 14)
  have hm1415 := MinimumMonotone91.minimum_monotone (by omega : 14 ≤ 15)
  have hm1516 := MinimumMonotone91.minimum_monotone (by omega : 15 ≤ 16)
  by_cases hd15_7 : 7 ≤ minimalDistinctDistances 15
  · left
    exact ⟨by omega, by omega, hfam15 hd15_7, hfam14⟩
  · by_cases hd13_6 : 6 ≤ minimalDistinctDistances 13
    · right; left
      have hd14_6 : minimalDistinctDistances 14 = 6 := by omega
      have hd15_6 : minimalDistinctDistances 15 = 6 := by omega
      refine ⟨hd14_6, hd15_6, ?_⟩
      exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
        14 (by omega) (hd14_6.trans hd15_6.symm) (by omega)
    · by_cases hd12_5 : 5 ≤ minimalDistinctDistances 12
      · right; right; left
        have hd12_eq : minimalDistinctDistances 12 = 5 := by omega
        have hd13_eq : minimalDistinctDistances 13 = 5 := by omega
        refine ⟨hd12_eq, hd13_eq, ?_⟩
        exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
          12 (by omega) (hd12_eq.trans hd13_eq.symm) (by omega)
      · right; right; right
        have hd12_le4 : minimalDistinctDistances 12 ≤ 4 := by omega
        refine ⟨hd12_le4, ?_⟩
        by_cases hplat11 : minimalDistinctDistances 11 = minimalDistinctDistances 12
        · left
          exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
            11 (by omega) hplat11 (by omega)
        · right
          have hplat10 : minimalDistinctDistances 10 = minimalDistinctDistances 11 := by omega
          exact Erdos91.UnconditionalNaturalDensityOne.plateau_not_unique_of_two_mul_lt_sub_one
            10 (by omega) hplat10 (by omega)

end Erdos91.CertifiedMultiDeletionFamilies10To15AndStepSevenDichotomy


end
