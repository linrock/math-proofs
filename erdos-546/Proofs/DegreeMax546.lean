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

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic


@[expose] public section

/-! Exact maximum-degree scalar interfaces. Taking the actual finite supremum
preserves the weighted deletion bound without a ceiling loss. -/

namespace Erdos546

theorem weighted_sup_bound {V : Type*} (S : Finset V) (d : V → ℕ) (k M : ℕ)
    (hdegree : ∀ v ∈ S, (k + 1) * d v ≤ M) :
    (k + 1) * S.sup d ≤ M := by
  have hquot : S.sup d ≤ M / (k + 1) := by
    apply Finset.sup_le
    intro v hv
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mpr
    simpa only [Nat.mul_comm] using hdegree v hv
  have hprod := (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mp hquot
  simpa only [Nat.mul_comm] using hprod

theorem sparse_degree_factor_bound (k D m a : ℕ) (hm : 0 < m)
    (hclique : (a : ℝ)^3 * Real.sqrt m ≤ k)
    (hdegree : (k + 1) * D ≤ 2 * m) :
    (a : ℝ)^3 * D ≤ 2 * Real.sqrt m := by
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hlow := mul_le_mul_of_nonneg_right hclique hD
  have hprod : ((k : ℝ) + 1) * D ≤ 2 * m := by exact_mod_cast hdegree
  have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
  apply (mul_le_mul_iff_left₀ hs).mp
  nlinarith only [hlow, hprod, hsq, hD]

end Erdos546
