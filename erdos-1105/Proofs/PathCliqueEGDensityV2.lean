module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Pure scalar density from a clique cap and an Erdős–Gallai-shaped numerical
hypothesis. This module asserts no graph theorem.
-/

namespace ErdosProblems.PathCliqueEGDensity

/-- A clique cap and the Erdős–Gallai edge inequality give the exact density
needed for each whole positive tail piece, including the `d=2,v=1` boundary. -/
theorem clique_eg_density (d v e : ℕ) (hd : 2 ≤ d) (hv : 1 ≤ v)
    (hclique : e ≤ v.choose 2) (hEG : 2 * e ≤ (d - 1) * v) :
    2 * d * (e + 1) ≤ (d * (d - 1) + 2) * v := by
  have hdsub : (d - 1) + 1 = d := by omega
  have hdsubR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast hdsub
  have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hclR : (e : ℝ) ≤ (v.choose 2 : ℝ) := by exact_mod_cast hclique
  rw [Nat.cast_choose_two ℝ v] at hclR
  have hEGR : 2 * (e : ℝ) ≤ ((d - 1 : ℕ) : ℝ) * (v : ℝ) := by
    exact_mod_cast hEG
  rw [hsub] at hEGR
  have hreal :
      2 * (d : ℝ) * ((e : ℝ) + 1) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + 2) * (v : ℝ) := by
    by_cases hvd : v ≤ d
    · have hvdR : (v : ℝ) ≤ (d : ℝ) := by exact_mod_cast hvd
      have hDV : (2 : ℝ) ≤ (d : ℝ) * (v : ℝ) := by
        have hprod := mul_nonneg
          (sub_nonneg.mpr hdR) (sub_nonneg.mpr hvR)
        nlinarith only [hdR, hvR, hprod]
      have hdeficit :
          0 ≤ ((d : ℝ) - (v : ℝ)) * ((d : ℝ) * (v : ℝ) - 2) :=
        mul_nonneg (sub_nonneg.mpr hvdR) (sub_nonneg.mpr hDV)
      have hweighted := mul_le_mul_of_nonneg_left hclR
        (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
      nlinarith only [hweighted, hdeficit]
    · have hlarge : d ≤ v := by omega
      have hlargeR : (d : ℝ) ≤ (v : ℝ) := by exact_mod_cast hlarge
      have hweighted := mul_le_mul_of_nonneg_left hEGR (Nat.cast_nonneg d)
      nlinarith only [hweighted, hlargeR]
  have hcast :
      ((2 * d * (e + 1) : ℕ) : ℝ) ≤
        (((d * (d - 1) + 2) * v : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, hsub] using hreal
  exact_mod_cast hcast

end ErdosProblems.PathCliqueEGDensity

