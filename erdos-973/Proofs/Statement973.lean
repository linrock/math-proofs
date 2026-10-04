module

/-
Copyright 2026 The Formal Conjectures Authors.

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

public import NewtonBridge973
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


@[expose] public section

/-!
# Exact statement and reindexing bridge for Erdős problem 973

`OriginalStatement` reproduces the mathematical right-hand side of
`Erdos973.erdos_973` in google-deepmind/formal-conjectures, from
`FormalConjectures/ErdosProblems/973.lean`, at commit
`5d65ac9b140a00051fe2827fb10911beb2201b3b`.
The source file's SHA-256 is
`8096c57f6beda47615d508145f22e2ac26c277a5251d3f45d3cbcad08b4f6712`.

The upstream file provides the problem statement, not a proof.  No incomplete
upstream declaration is imported.  The theorem below is a logical bridge from
an eventual lower bound, supplied as an explicit hypothesis, to the negation
of the original statement.  A complete solution must discharge that hypothesis.

The normalization, exterior condition, excluded first power, included endpoint
`n + 1`, strict inequality, real exponent, and quantifier order are unchanged.
-/

noncomputable section

open scoped BigOperators
open Finset Filter

namespace Erdos973

/-- The exact mathematical right-hand side of the pinned upstream statement. -/
def OriginalStatement : Prop :=
  ∃ C : ℝ, C > 1 ∧
    ∀ n : ℕ, n ≥ 2 → ∃ z : ℕ → ℂ,
      z 1 = 1 ∧
      (∀ i ∈ Icc 1 n, 1 ≤ ‖z i‖) ∧
      (∀ k ∈ Icc 2 (n + 1), ‖∑ i ∈ Icc 1 n, z i ^ k‖ < C ^ (-(n : ℝ)))

/-- Reindexing retains every indexed point and its multiplicity. -/
theorem powerSum_fin_reindex (n k : ℕ) (z : ℕ → ℂ) :
    powerSum Finset.univ (fun i : Fin n => z (i.val + 1)) k =
      ∑ i ∈ Finset.Icc 1 n, z i ^ k := by
  classical
  unfold powerSum
  apply Finset.sum_bij (fun i _ => i.val + 1)
  · intro i _
    exact Finset.mem_Icc.mpr (by omega)
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i _
    rfl

/-- Any uniform eventual lower bound at every fixed exponential scale refutes
the exact original all-orders demand.  The analytic input remains explicit. -/
theorem not_original_of_eventual_lower_bound
    (h : ∀ C : ℝ, 1 < C → ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ,
      (∀ i, 1 ≤ ‖z i‖) →
      ∃ k ∈ Finset.Icc 2 (n + 1),
        C ^ (-(n : ℝ)) ≤ ‖powerSum Finset.univ z k‖) :
    ¬ OriginalStatement := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h C hC)
  let n : ℕ := max N 2
  have hnN : N ≤ n := le_max_left _ _
  have hn2 : 2 ≤ n := le_max_right _ _
  obtain ⟨z, _, hz, hsmall⟩ := hall n hn2
  obtain ⟨k, hk, hlower⟩ := hN n hnN (fun i : Fin n => z (i.val + 1))
    (fun i => hz _ (Finset.mem_Icc.mpr (by omega)))
  rw [powerSum_fin_reindex] at hlower
  exact (not_lt_of_ge hlower) (hsmall k hk)

end Erdos973
