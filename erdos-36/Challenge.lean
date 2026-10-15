module

/-
Copyright 2026 The Formal Conjectures Authors.
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

Adaptation notice: Linmiao Xu adapted `Overlap`, `MaxOverlap`, `M`,
`MinOverlapQuotient`, and the minimum-overlap lower/upper bound statements from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/36.lean`)
and added Fekete limit existence, Moser's $\sqrt{2}/4$ bound, the combined
Moser–Scherk cap-and-moment bound, and exact values through $M(15) = 6$ for
this standalone Lean 4 benchmark in 2026. This file imports only Mathlib.
-/

public import Mathlib

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace Erdos36

/-- Number of solutions to $a - b = k$ with $a \in A$ and $b \in B$. -/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A.product B).filter <| fun (a, b) => a - b = k).card

/-- Maximum overlap over all integer differences $k \in \mathbb{Z}$. -/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ :=
  iSup <| Overlap A B

/-- Minimum maximum overlap $M(n)$ over all balanced partitions $(A, B)$ of $\{1, \dots, 2n\}$. -/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/-- Normalized minimum overlap quotient $M(N) / N$. -/
noncomputable def MinOverlapQuotient (N : ℕ) : ℝ :=
  (M N : ℝ) / N

/-- Fekete limit existence for the minimum overlap quotient (`FormalConjectures` `erdos_36.variants.exists`):
$\liminf_{N \to \infty} M(N)/N = \limsup_{N \to \infty} M(N)/N$. -/
theorem liminf_eq_limsup_minOverlapQuotient :
    atTop.liminf MinOverlapQuotient = atTop.limsup MinOverlapQuotient := by
  sorry

/-- Convergence of $M(N)/N$ to its Fekete limit (`FormalConjectures` `erdos_36.variants.exists`). -/
theorem tendsto_minOverlapQuotient_liminf :
    atTop.Tendsto MinOverlapQuotient (𝓝 (atTop.liminf MinOverlapQuotient)) := by
  sorry

/-- Erdős's 1955 lower bound $1/4 \le \liminf M(N)/N$ (`FormalConjectures` `minimum_overlap.variants.lower.erdos_1955`). -/
theorem minimum_overlap_variants_lower_erdos_1955 :
    (1 : ℝ) / 4 ≤ atTop.liminf MinOverlapQuotient := by
  sorry

/-- Scherk's 1955 lower bound $1 - 1/\sqrt{2} < \liminf M(N)/N$ (`FormalConjectures` `minimum_overlap.variants.lower.scherk_1955`). -/
theorem minimum_overlap_variants_lower_scherk_1955 :
    1 - (Real.sqrt 2)⁻¹ < atTop.liminf MinOverlapQuotient := by
  sorry

/-- Świerczkowski's 1958 lower bound $(4 - \sqrt{6})/5 < \liminf M(N)/N$ (`FormalConjectures` `minimum_overlap.variants.lower.swierczkowski_1958`). -/
theorem minimum_overlap_variants_lower_swierczkowski_1958 :
    (4 - 6 ^ ((1 : ℝ) / 2)) / 5 < atTop.liminf MinOverlapQuotient := by
  sorry

/-- Moser's 1959 second-moment lower bound $\sqrt{2}/4 \le \liminf M(N)/N$. -/
theorem moser_sqrt_two_div_four_le_liminf :
    Real.sqrt 2 / 4 ≤ atTop.liminf MinOverlapQuotient := by
  sorry

/-- Erdős's 1955 upper bound $\limsup M(N)/N \le 1/2$ (`FormalConjectures` `minimum_overlap.variants.upper.erdos_1955`). -/
theorem minimum_overlap_variants_upper_erdos_1955 :
    atTop.limsup MinOverlapQuotient ≤ (1 : ℝ) / 2 := by
  sorry

/-- Combined Moser–Scherk cap-and-moment lower bound on $M(n)$ for arbitrary window radius $R$. -/
theorem moser_scherk_combined_le_M (n R : ℕ) :
    12 * R ^ 2 * n ^ 2 + 6 * R ^ 2 * M n +
      6 * (∑ k ∈ Finset.range R,
        (R ^ 2 - (k + 1) ^ 2) * (2 * M n - (2 * n - 1 - k))) ≤
      8 * n ^ 4 + 4 * R * (4 * R ^ 2 - 1) * M n := by
  sorry

/-- Exact finite values $M(1)..M(4), M(6)..M(9), M(12), M(14), M(15)$ (OEIS A004133). -/
theorem exact_values_M :
    M 1 = 1 ∧ M 2 = 1 ∧ M 3 = 2 ∧ M 6 = 3 ∧ M 7 = 3 ∧
      M 8 = 4 ∧ M 9 = 4 ∧ M 12 = 5 ∧ M 14 = 6 ∧ M 15 = 6 := by
  sorry

end Erdos36
