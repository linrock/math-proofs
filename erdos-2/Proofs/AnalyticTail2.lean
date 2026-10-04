module

public import Mathlib


@[expose] public section

/-!
# Sixth-power Euler factor comparison and log-power tail summability

Proves the elementary inequality $1 + 2(3q - 1)/(q - 1)^2 \le (q / (q - 1))^6$
for $q \ge 2$ and the summability of $(\log n)^k / (n - 1)^2$ over $n \in \mathbb{N}$.
-/

open scoped BigOperators
open Filter Asymptotics Topology

namespace Erdos2.Analytic

theorem deltaHalfFactor_le_inverseEuler_pow_six (q : ℝ) (hq : 2 ≤ q) :
    1 + 2 * (3 * q - 1) / (q - 1) ^ 2 ≤ (q / (q - 1)) ^ 6 := by
  have hd : 0 < q - 1 := by linarith
  let t : ℝ := 1 / (q - 1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have heq : 1 + 2 * (3 * q - 1) / (q - 1) ^ 2 = 1 + 6 * t + 4 * t ^ 2 := by
    dsimp [t]
    field_simp
    ring
  have heq' : q / (q - 1) = 1 + t := by
    dsimp [t]
    field_simp
    ring
  rw [heq, heq']
  nlinarith [pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
    pow_nonneg ht 6, sq_nonneg t]

theorem summable_log_pow_div_square (k : ℕ) :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ k / (n : ℝ) ^ 2) := by
  have hlog : (fun x : ℝ => Real.log x ^ k) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (s := 1 / 2) (by norm_num))
  have hb := tendsto_natCast_atTop_atTop.eventually
    (hlog.bound (c := 1) (by norm_num))
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).of_norm_bounded_eventually_nat
  filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn' : ‖Real.log (n : ℝ) ^ k‖ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn
  calc
    ‖Real.log (n : ℝ) ^ k / (n : ℝ) ^ 2‖ =
        ‖Real.log (n : ℝ) ^ k‖ / (n : ℝ) ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hn' (sq_nonneg _)
    _ = (n : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_sub hnpos]
      norm_num

theorem deltaHalfProduct_le_inverseEuler_pow_six (s t : Finset ℕ)
    (hst : s ⊆ t) (ht : ∀ q ∈ t, Nat.Prime q) :
    (∏ q ∈ s, (1 + 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2)) ≤
      (∏ q ∈ t, ((q : ℝ) / ((q : ℝ) - 1))) ^ 6 := by
  have hq (q : ℕ) (hqt : q ∈ t) : (2 : ℝ) ≤ q := by
    exact_mod_cast (ht q hqt).two_le
  have hpos (q : ℕ) (hqt : q ∈ t) : 0 ≤ ((q : ℝ) / ((q : ℝ) - 1)) := by
    apply div_nonneg (Nat.cast_nonneg q)
    linarith [hq q hqt]
  have hprod : (∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1))) ≤
      (∏ q ∈ t, ((q : ℝ) / ((q : ℝ) - 1))) :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hst
      (fun q hqs => hpos q (hst hqs))
      (fun q hqt _ => by
        apply (le_div_iff₀ (by linarith [hq q hqt])).mpr
        linarith)
  calc
    _ ≤ ∏ q ∈ s, (((q : ℝ) / ((q : ℝ) - 1)) ^ 6) := by
      apply Finset.prod_le_prod₀
      · intro q hqs
        have h2 := hq q (hst hqs)
        have : 0 ≤ 3 * (q : ℝ) - 1 := by linarith
        positivity
      · intro q hqs
        exact deltaHalfFactor_le_inverseEuler_pow_six _ (hq q (hst hqs))
    _ = (∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1))) ^ 6 :=
      Finset.prod_pow _ _ _
    _ ≤ _ := pow_le_pow_left₀ (Finset.prod_nonneg fun q hqs => hpos q (hst hqs)) hprod 6

theorem summable_log_pow_div_sub_one_square (k : ℕ) :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ k / ((n : ℝ) - 1) ^ 2) := by
  apply ((summable_log_pow_div_square k).mul_left 4).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hdpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.log (n : ℝ) ^ k :=
    pow_nonneg (Real.log_nonneg (by linarith)) _
  have hratio : 1 / ((n : ℝ) - 1) ^ 2 ≤ 4 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) (sq_pos_of_pos hnpos)).mpr
    nlinarith
  rw [Real.norm_of_nonneg (div_nonneg hL (sq_nonneg _))]
  calc
    _ = Real.log (n : ℝ) ^ k * (1 / ((n : ℝ) - 1) ^ 2) := by ring
    _ ≤ Real.log (n : ℝ) ^ k * (4 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hratio hL
    _ = _ := by ring

end Erdos2.Analytic
